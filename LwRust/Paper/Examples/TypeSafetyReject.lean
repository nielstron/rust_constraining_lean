import LwRust.Paper.Examples.Operational
import LwRust.Paper.Soundness.Helpers.RuntimeFacts
import LwRust.Paper.Soundness.Lemma_4_10_Progress

/-!
Build-checked rejected examples.

These files state rejection as negated typing derivations.  That keeps the
Lean build green while showing that the type-and-borrow safety theorem cannot
be applied to the program.
-/

namespace LwRust
namespace Paper

open Core

def invalidBorrowIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := InvalidBorrowExample.l }

def invalidBorrowYSlot : EnvSlot :=
  { ty := .ty (Ty.borrow true [InvalidBorrowExample.x]),
    lifetime := InvalidBorrowExample.l }

/--
Runtime references are not source-level constants over the empty store typing.
This is the small closed-form version of the paper's distinction between
source programs and values created by the operational semantics.
-/
def rawBorrowedReferenceConstant : Term :=
  .val (.ref { location := .var "x", owner := false })

theorem rawBorrowedReferenceConstant_rejected :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty Lifetime.root
        rawBorrowedReferenceConstant ty env := by
  rintro ⟨ty, env, htyping⟩
  unfold rawBorrowedReferenceConstant at htyping
  cases htyping with
  | const hvalue =>
      cases hvalue with
      | ref hlookup =>
          simp [StoreTyping.empty] at hlookup

def boxedRawBorrowedReferenceConstant : Term :=
  .box rawBorrowedReferenceConstant

theorem boxedRawBorrowedReferenceConstant_rejected :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty Lifetime.root
        boxedRawBorrowedReferenceConstant ty env := by
  rintro ⟨ty, env, htyping⟩
  unfold boxedRawBorrowedReferenceConstant rawBorrowedReferenceConstant at htyping
  cases htyping with
  | box hinner =>
      cases hinner with
      | const hvalue =>
          cases hvalue with
          | ref hlookup =>
              simp [StoreTyping.empty] at hlookup

/--
Paper Section 3.3 example (10), after the invalid borrow has escaped its inner
block: dereferencing `w` is neither terminal nor step-able.
-/
theorem escapingBorrow_stuck_after_inner_drop :
    ¬ ProgressResult InvalidEscapingBorrowExample.Sw
      InvalidEscapingBorrowExample.l
      (.move (.deref (.var "w"))) := by
  intro hprogress
  rcases hprogress with hterminal | ⟨store', term', hstep⟩
  · simp [Terminal] at hterminal
  · exact InvalidEscapingBorrowExample.deref_w_after_z_dropped_is_stuck
      ⟨store', term', hstep⟩

/--
Paper Section 3.3 example (9).  This is the exact program
`{ let mut x = 0; let mut y = &mut x; x = 1; }`.
-/
theorem invalidBorrowExample_rejected :
    ¬ ∃ ty env,
      TermTyping Env.empty StoreTyping.empty InvalidBorrowExample.l
        InvalidBorrowExample.invalidProgram ty env := by
  rintro ⟨ty, env, htyping⟩
  unfold InvalidBorrowExample.invalidProgram at htyping
  cases htyping with
  | block _hchild hbody _hwellTy _hdrop =>
      cases hbody with
      | cons hdeclareX htail =>
          cases htail with
          | cons hdeclareY htail2 =>
              cases htail2 with
              | singleton hassign =>
                  cases hdeclareX with
                  | declare _freshX hinitX _freshXOut _cohX hxEnv =>
                      cases hinitX with
                      | const _ =>
                          cases hdeclareY with
                          | declare _freshY hinitY _freshYOut _cohY hyEnv =>
                              cases hinitY with
                              | mutBorrow _hLvY _mutableY _notWriteY =>
                                  rename_i _valueLifetimeY borrowedTy
                                  cases hassign with
                                  | assign _hRhs _hLhsPost _hshape _hwell
                                      hwrite _hranked _hrhsWF hnotWrite =>
                                      cases _hRhs with
                                      | const hvalue =>
                                      cases hvalue
                                      cases hwrite with
                                      | intro hslot hupdate =>
                                          subst hxEnv
                                          subst hyEnv
                                          cases hupdate with
                                          | strong =>
                                          exact hnotWrite (by
                                            left
                                            refine ⟨"y", [InvalidBorrowExample.x],
                                              InvalidBorrowExample.x, ?_,
                                              by simp, by simp [PathConflicts]⟩
                                            refine ⟨
                                              { ty := .ty (Ty.borrow true
                                                  [InvalidBorrowExample.x]),
                                                lifetime := InvalidBorrowExample.l },
                                              ?_, PartialTyContains.here⟩
                                            simp [Env.update, InvalidBorrowExample.x,
                                              InvalidBorrowExample.l, LVal.base])
              | cons _hhead htail => cases htail

/-- Paper Section 6.1.3's joined environment after
`if ... { p = &mut a; } else { q = &mut a; }`. -/
def rootIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def paperConditionalPSlot : EnvSlot :=
  { ty := .ty (Ty.borrow true [.var "x", .var "a"]),
    lifetime := Lifetime.root }

def paperConditionalQSlot : EnvSlot :=
  { ty := .ty (Ty.borrow true [.var "y", .var "a"]),
    lifetime := Lifetime.root }

def paperConditionalJoinEnv : Env :=
  (((((Env.empty.update "a" rootIntSlot).update "x" rootIntSlot).update
    "y" rootIntSlot).update "p" paperConditionalPSlot).update
    "q" paperConditionalQSlot)

def paperRejectedIfElse : Term :=
  .ite (.val (.bool true))
    (.assign (.var "p") (.borrow true (.var "a")))
    (.assign (.var "q") (.borrow true (.var "a")))

/--
The paper notes that the Section 6.1.3 conditional join is not borrow safe:
`p` and `q` may both contain mutable borrows whose target lists include `a`.
Our `T-If` rule rejects this by requiring `BorrowSafeEnv` for the joined
environment of `paperRejectedIfElse`.
-/
theorem paperConditionalJoinEnv_not_borrowSafe :
    ¬ BorrowSafeEnv paperConditionalJoinEnv := by
  intro hsafe
  have hp : paperConditionalJoinEnv ⊢ "p" ↝
      (.borrow true [.var "x", .var "a"]) := by
    refine ⟨paperConditionalPSlot, ?_, PartialTyContains.here⟩
    simp [paperConditionalJoinEnv, paperConditionalPSlot, paperConditionalQSlot,
      rootIntSlot, Env.update]
  have hq : paperConditionalJoinEnv ⊢ "q" ↝
      (.borrow true [.var "y", .var "a"]) := by
    refine ⟨paperConditionalQSlot, ?_, PartialTyContains.here⟩
    simp [paperConditionalJoinEnv, paperConditionalPSlot, paperConditionalQSlot,
      rootIntSlot, Env.update]
  have hpq : "p" = "q" :=
    hsafe "p" "q" true [.var "x", .var "a"] [.var "y", .var "a"]
      (.var "a") (.var "a") hp hq (by simp) (by simp)
      (by simp [PathConflicts, LVal.base])
  contradiction

theorem paperRejectedIfElse_join_rejected :
    ¬ BorrowSafeEnv paperConditionalJoinEnv :=
  paperConditionalJoinEnv_not_borrowSafe

/-! ### Raw `T-If` without block-scoped branches can leak declarations.

If the core `.ite` form is allowed to take arbitrary branch terms, then
same-shape join evidence is not enough to recover coherence.  The rule can join
two coherent branch outputs into an incoherent environment:

```
if true let mut b = &x else let mut b = &y
```

where `x : int` and `y : bool`.  The join widens `b` to `&[x,y]`, but that
target list has no joint type. This is not a block-scoped source conditional:
the branch declarations leak precisely because the branches are raw `let`
terms rather than blocks.
-/

def incoherentIfIntSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def incoherentIfBoolSlot : EnvSlot :=
  { ty := .ty .bool, lifetime := Lifetime.root }

def incoherentIfBXSlot : EnvSlot :=
  { ty := .ty (.borrow false [.var "x"]), lifetime := Lifetime.root }

def incoherentIfBYSlot : EnvSlot :=
  { ty := .ty (.borrow false [.var "y"]), lifetime := Lifetime.root }

def incoherentIfBJoinSlot : EnvSlot :=
  { ty := .ty (.borrow false [.var "x", .var "y"]),
    lifetime := Lifetime.root }

def incoherentIfXEnv : Env :=
  Env.empty.update "x" incoherentIfIntSlot

def incoherentIfXYEnv : Env :=
  incoherentIfXEnv.update "y" incoherentIfBoolSlot

def incoherentIfXBranchEnv : Env :=
  incoherentIfXYEnv.update "b" incoherentIfBXSlot

def incoherentIfYBranchEnv : Env :=
  incoherentIfXYEnv.update "b" incoherentIfBYSlot

def incoherentIfJoinEnv : Env :=
  incoherentIfXYEnv.update "b" incoherentIfBJoinSlot

def incoherentIfTerm : Term :=
  .ite (.val (.bool true))
    (.letMut "b" (.borrow false (.var "x")))
    (.letMut "b" (.borrow false (.var "y")))

theorem incoherentIfTerm_not_controlBodiesAreBlocks :
    ¬ incoherentIfTerm.controlBodiesAreBlocks := by
  simp [incoherentIfTerm, Term.controlBodiesAreBlocks, Term.isBlock]

theorem incoherentIfTerm_sourceTerm : SourceTerm incoherentIfTerm := by
  intro value hmem
  simp [incoherentIfTerm, termValues] at hmem
  subst value
  simp [SourceValue]

theorem incoherentIfTerm_not_blockScopedSourceTerm :
    ¬ BlockScopedSourceTerm incoherentIfTerm := by
  intro hsource
  exact incoherentIfTerm_not_controlBodiesAreBlocks
    (BlockScopedSourceTerm.controlTerm hsource)

def incoherentIfPrefix : List Term :=
  [.letMut "x" (.val (.int 0)), .letMut "y" (.val (.bool false))]

theorem incoherentIfXEnv_lval_facts {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    LValTyping incoherentIfXEnv lv partialTy lifetime →
    lv = .var "x" ∧ partialTy = .ty .int ∧ lifetime = Lifetime.root := by
  intro htyping
  induction lv generalizing partialTy lifetime with
  | var name =>
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, hslotLife⟩
      by_cases hx : name = "x"
      · subst hx
        have hslotEq : slot = incoherentIfIntSlot := by
          have hxSlot :
              incoherentIfXEnv.slotAt "x" =
                some incoherentIfIntSlot := by
            simp [incoherentIfXEnv, incoherentIfIntSlot, Env.update]
          exact Option.some.inj (hslot.symm.trans hxSlot)
        subst hslotEq
        simp [incoherentIfIntSlot] at hslotTy hslotLife
        simp [hslotTy, hslotLife]
      · have hnone : incoherentIfXEnv.slotAt name = none := by
          simp [incoherentIfXEnv, Env.update, Env.empty, hx]
        rw [hslot] at hnone
        cases hnone
  | deref lv ih =>
      cases htyping with
      | box hinner =>
          rcases ih hinner with ⟨_, hpartial, _⟩
          cases hpartial
      | borrow hinner _htargets =>
          rcases ih hinner with ⟨_, hpartial, _⟩
          cases hpartial

theorem incoherentIfXYEnv_lval_facts {lv : LVal} {partialTy : PartialTy}
    {lifetime : Lifetime} :
    LValTyping incoherentIfXYEnv lv partialTy lifetime →
    (lv = .var "x" ∧ partialTy = .ty .int ∧ lifetime = Lifetime.root) ∨
      (lv = .var "y" ∧ partialTy = .ty .bool ∧ lifetime = Lifetime.root) := by
  intro htyping
  induction lv generalizing partialTy lifetime with
  | var name =>
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, hslotLife⟩
      by_cases hy : name = "y"
      · subst hy
        have hslotEq : slot = incoherentIfBoolSlot := by
          have hySlot :
              incoherentIfXYEnv.slotAt "y" =
                some incoherentIfBoolSlot := by
            simp [incoherentIfXYEnv, incoherentIfBoolSlot, Env.update]
          exact Option.some.inj (hslot.symm.trans hySlot)
        subst hslotEq
        right
        simp [incoherentIfBoolSlot] at hslotTy hslotLife
        simp [hslotTy, hslotLife]
      · by_cases hx : name = "x"
        · subst hx
          have hslotEq : slot = incoherentIfIntSlot := by
            have hxSlot :
                incoherentIfXYEnv.slotAt "x" =
                  some incoherentIfIntSlot := by
              simp [incoherentIfXYEnv, incoherentIfXEnv,
                incoherentIfIntSlot, incoherentIfBoolSlot, Env.update]
            exact Option.some.inj (hslot.symm.trans hxSlot)
          subst hslotEq
          left
          simp [incoherentIfIntSlot] at hslotTy hslotLife
          simp [hslotTy, hslotLife]
        · have hnone : incoherentIfXYEnv.slotAt name = none := by
            simp [incoherentIfXYEnv, incoherentIfXEnv, Env.update,
              Env.empty, hy, hx]
          rw [hslot] at hnone
          cases hnone
  | deref lv ih =>
      cases htyping with
      | box hinner =>
          rcases ih hinner with ⟨_, hpartial, _⟩ | ⟨_, hpartial, _⟩
          · cases hpartial
          · cases hpartial
      | borrow hinner _htargets =>
          rcases ih hinner with ⟨_, hpartial, _⟩ | ⟨_, hpartial, _⟩
          · cases hpartial
          · cases hpartial

theorem incoherentIfXY_x_typing :
    LValTyping incoherentIfXYEnv (.var "x") (.ty .int) Lifetime.root := by
  exact @LValTyping.var incoherentIfXYEnv "x" incoherentIfIntSlot (by
    simp [incoherentIfXYEnv, incoherentIfXEnv, incoherentIfIntSlot,
      incoherentIfBoolSlot, Env.update])

theorem incoherentIfXY_y_typing :
    LValTyping incoherentIfXYEnv (.var "y") (.ty .bool) Lifetime.root := by
  exact @LValTyping.var incoherentIfXYEnv "y" incoherentIfBoolSlot (by
    simp [incoherentIfXYEnv, incoherentIfBoolSlot, Env.update])

theorem incoherentIfXY_no_readProhibited (lv : LVal) :
    ¬ ReadProhibited incoherentIfXYEnv lv := by
  intro hread
  rcases hread with ⟨root, targets, target, hcontains, _htarget, _hconflict⟩
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hy : root = "y"
  · subst hy
    have hslotEq : slot = incoherentIfBoolSlot := by
      have hySlot :
          incoherentIfXYEnv.slotAt "y" = some incoherentIfBoolSlot := by
        simp [incoherentIfXYEnv, incoherentIfBoolSlot, Env.update]
      exact Option.some.inj (hslot.symm.trans hySlot)
    subst hslotEq
    simp [incoherentIfBoolSlot] at hcontainsTy
    cases hcontainsTy
  · by_cases hx : root = "x"
    · subst hx
      have hslotEq : slot = incoherentIfIntSlot := by
        have hxSlot :
            incoherentIfXYEnv.slotAt "x" = some incoherentIfIntSlot := by
          simp [incoherentIfXYEnv, incoherentIfXEnv, incoherentIfIntSlot,
            incoherentIfBoolSlot, Env.update]
        exact Option.some.inj (hslot.symm.trans hxSlot)
      subst hslotEq
      simp [incoherentIfIntSlot] at hcontainsTy
      cases hcontainsTy
    · have hnone : incoherentIfXYEnv.slotAt root = none := by
        simp [incoherentIfXYEnv, incoherentIfXEnv, Env.update, Env.empty,
          hy, hx]
      rw [hslot] at hnone
      cases hnone

theorem incoherentIf_freshInt_obligations :
    FreshUpdateCoherenceObligations Env.empty "x" .int Lifetime.root := by
  constructor
  · intro lv mutable targets borrowLifetime _hbase htyping
    rcases incoherentIfXEnv_lval_facts htyping with ⟨_, hpartial, _⟩
    cases hpartial
  · intro lv mutable targets borrowLifetime _hbase htyping
    rcases incoherentIfXEnv_lval_facts htyping with ⟨_, hpartial, _⟩
    cases hpartial

theorem incoherentIf_freshBool_obligations :
    FreshUpdateCoherenceObligations incoherentIfXEnv "y" .bool
      Lifetime.root := by
  constructor
  · intro lv mutable targets borrowLifetime _hbase htyping
    rcases incoherentIfXYEnv_lval_facts htyping with
      ⟨_, hpartial, _⟩ | ⟨_, hpartial, _⟩
    · cases hpartial
    · cases hpartial
  · intro lv mutable targets borrowLifetime _hbase htyping
    rcases incoherentIfXYEnv_lval_facts htyping with
      ⟨_, hpartial, _⟩ | ⟨_, hpartial, _⟩
    · cases hpartial
    · cases hpartial

theorem incoherentIf_declareX_typing :
    TermTyping Env.empty StoreTyping.empty Lifetime.root
      (.letMut "x" (.val (.int 0))) .unit incoherentIfXEnv := by
  exact TermTyping.declare
    (by simp [Env.fresh, Env.empty])
    (TermTyping.const ValueTyping.int)
    (by simp [Env.fresh, Env.empty])
    incoherentIf_freshInt_obligations
    rfl

theorem incoherentIf_declareY_typing :
    TermTyping incoherentIfXEnv StoreTyping.empty Lifetime.root
      (.letMut "y" (.val (.bool false))) .unit incoherentIfXYEnv := by
  exact TermTyping.declare
    (by simp [Env.fresh, incoherentIfXEnv, Env.update, Env.empty])
    (TermTyping.const ValueTyping.bool)
    (by simp [Env.fresh, incoherentIfXEnv, Env.update, Env.empty])
    incoherentIf_freshBool_obligations
    rfl

theorem incoherentIfPrefix_typing :
    TermListTyping Env.empty StoreTyping.empty Lifetime.root
      incoherentIfPrefix .unit incoherentIfXYEnv := by
  unfold incoherentIfPrefix
  exact TermListTyping.cons incoherentIf_declareX_typing
    (TermListTyping.singleton incoherentIf_declareY_typing)

theorem incoherentIfXBranch_b_typing :
    LValTyping incoherentIfXBranchEnv (.var "b")
      (.ty (.borrow false [.var "x"])) Lifetime.root := by
  exact @LValTyping.var incoherentIfXBranchEnv "b" incoherentIfBXSlot (by
    simp [incoherentIfXBranchEnv, incoherentIfBXSlot, Env.update])

theorem incoherentIfYBranch_b_typing :
    LValTyping incoherentIfYBranchEnv (.var "b")
      (.ty (.borrow false [.var "y"])) Lifetime.root := by
  exact @LValTyping.var incoherentIfYBranchEnv "b" incoherentIfBYSlot (by
    simp [incoherentIfYBranchEnv, incoherentIfBYSlot, Env.update])

theorem incoherentIfXBranch_x_typing :
    LValTyping incoherentIfXBranchEnv (.var "x") (.ty .int)
      Lifetime.root := by
  exact LValTyping.update_fresh_one (env := incoherentIfXYEnv)
    (x := "b") (slot := incoherentIfBXSlot) (by
      simp [Env.fresh, incoherentIfXYEnv, incoherentIfXEnv, Env.update,
        Env.empty]) incoherentIfXY_x_typing

theorem incoherentIfYBranch_y_typing :
    LValTyping incoherentIfYBranchEnv (.var "y") (.ty .bool)
      Lifetime.root := by
  exact LValTyping.update_fresh_one (env := incoherentIfXYEnv)
    (x := "b") (slot := incoherentIfBYSlot) (by
      simp [Env.fresh, incoherentIfXYEnv, incoherentIfXEnv, Env.update,
        Env.empty]) incoherentIfXY_y_typing

theorem incoherentIfXBranch_no_box {lv : LVal} {inner : PartialTy}
    {lifetime : Lifetime} :
    ¬ LValTyping incoherentIfXBranchEnv lv (.box inner) lifetime := by
  intro htyping
  induction lv generalizing inner lifetime with
  | var name =>
      rcases LValTyping.var_inv htyping with
        ⟨slot, hslot, hslotTy, hslotLife⟩
      by_cases hb : name = "b"
      · subst hb
        have hslotEq : slot = incoherentIfBXSlot := by
          have hbSlot :
              incoherentIfXBranchEnv.slotAt "b" = some incoherentIfBXSlot := by
            simp [incoherentIfXBranchEnv, incoherentIfBXSlot, Env.update]
          exact Option.some.inj (hslot.symm.trans hbSlot)
        subst hslotEq
        simp [incoherentIfBXSlot] at hslotTy
      · have hxyTyping : LValTyping incoherentIfXYEnv (.var name)
            (.box inner) lifetime := by
          have hxyVar : LValTyping incoherentIfXYEnv (.var name)
              slot.ty slot.lifetime :=
            @LValTyping.var incoherentIfXYEnv name slot (by
            simpa [incoherentIfXBranchEnv, Env.update, hb] using hslot)
          simpa [hslotTy, hslotLife] using hxyVar
        rcases incoherentIfXYEnv_lval_facts hxyTyping with
          ⟨_, hpartial, _⟩ | ⟨_, hpartial, _⟩
        · cases hpartial
        · cases hpartial
  | deref lv ih =>
      cases htyping with
      | box hinner =>
          exact ih hinner
      | borrow _hinner htargets =>
          exact LValTargetsTyping.not_box htargets

theorem incoherentIfYBranch_no_box {lv : LVal} {inner : PartialTy}
    {lifetime : Lifetime} :
    ¬ LValTyping incoherentIfYBranchEnv lv (.box inner) lifetime := by
  intro htyping
  induction lv generalizing inner lifetime with
  | var name =>
      rcases LValTyping.var_inv htyping with
        ⟨slot, hslot, hslotTy, hslotLife⟩
      by_cases hb : name = "b"
      · subst hb
        have hslotEq : slot = incoherentIfBYSlot := by
          have hbSlot :
              incoherentIfYBranchEnv.slotAt "b" = some incoherentIfBYSlot := by
            simp [incoherentIfYBranchEnv, incoherentIfBYSlot, Env.update]
          exact Option.some.inj (hslot.symm.trans hbSlot)
        subst hslotEq
        simp [incoherentIfBYSlot] at hslotTy
      · have hxyTyping : LValTyping incoherentIfXYEnv (.var name)
            (.box inner) lifetime := by
          have hxyVar : LValTyping incoherentIfXYEnv (.var name)
              slot.ty slot.lifetime :=
            @LValTyping.var incoherentIfXYEnv name slot (by
            simpa [incoherentIfYBranchEnv, Env.update, hb] using hslot)
          simpa [hslotTy, hslotLife] using hxyVar
        rcases incoherentIfXYEnv_lval_facts hxyTyping with
          ⟨_, hpartial, _⟩ | ⟨_, hpartial, _⟩
        · cases hpartial
        · cases hpartial
  | deref lv ih =>
      cases htyping with
      | box hinner =>
          exact ih hinner
      | borrow _hinner htargets =>
          exact LValTargetsTyping.not_box htargets

theorem incoherentIfXBranch_x_targets_not_borrow {mutable : Bool}
    {targets : List LVal} {lifetime : Lifetime} :
    ¬ LValTargetsTyping incoherentIfXBranchEnv [.var "x"]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htargets
  cases htargets with
  | singleton htarget =>
      rcases LValTyping.var_inv htarget with ⟨slot, hslot, hslotTy, _⟩
      have hslotEq : slot = incoherentIfIntSlot := by
        have hxSlot :
            incoherentIfXBranchEnv.slotAt "x" = some incoherentIfIntSlot := by
          simp [incoherentIfXBranchEnv, incoherentIfXYEnv, incoherentIfXEnv,
            incoherentIfIntSlot, incoherentIfBoolSlot, incoherentIfBXSlot,
            Env.update]
        exact Option.some.inj (hslot.symm.trans hxSlot)
      subst hslotEq
      simp [incoherentIfIntSlot] at hslotTy
  | cons _ hrest _ _ =>
      cases hrest

theorem incoherentIfYBranch_y_targets_not_borrow {mutable : Bool}
    {targets : List LVal} {lifetime : Lifetime} :
    ¬ LValTargetsTyping incoherentIfYBranchEnv [.var "y"]
      (.ty (.borrow mutable targets)) lifetime := by
  intro htargets
  cases htargets with
  | singleton htarget =>
      rcases LValTyping.var_inv htarget with ⟨slot, hslot, hslotTy, _⟩
      have hslotEq : slot = incoherentIfBoolSlot := by
        have hySlot :
            incoherentIfYBranchEnv.slotAt "y" = some incoherentIfBoolSlot := by
          simp [incoherentIfYBranchEnv, incoherentIfXYEnv,
            incoherentIfBoolSlot, incoherentIfBYSlot, Env.update]
        exact Option.some.inj (hslot.symm.trans hySlot)
      subst hslotEq
      simp [incoherentIfBoolSlot] at hslotTy
  | cons _ hrest _ _ =>
      cases hrest

theorem incoherentIfXBranch_borrow_facts {lv : LVal} {mutable : Bool}
    {targets : List LVal} {lifetime : Lifetime} :
    LValTyping incoherentIfXBranchEnv lv
      (.ty (.borrow mutable targets)) lifetime →
    lv = .var "b" ∧ mutable = false ∧ targets = [.var "x"] ∧
      lifetime = Lifetime.root := by
  intro htyping
  induction lv generalizing mutable targets lifetime with
  | var name =>
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, hslotLife⟩
      by_cases hb : name = "b"
      · subst hb
        have hslotEq : slot = incoherentIfBXSlot := by
          have hbSlot :
              incoherentIfXBranchEnv.slotAt "b" =
                some incoherentIfBXSlot := by
            simp [incoherentIfXBranchEnv, incoherentIfBXSlot, Env.update]
          exact Option.some.inj (hslot.symm.trans hbSlot)
        subst hslotEq
        simp [incoherentIfBXSlot] at hslotTy hslotLife
        simp [hslotTy, hslotLife]
      · have hxyTyping :
            LValTyping incoherentIfXYEnv (.var name)
              (.ty (.borrow mutable targets)) lifetime := by
          have hxyVar : LValTyping incoherentIfXYEnv (.var name)
              slot.ty slot.lifetime :=
            @LValTyping.var incoherentIfXYEnv name slot (by
            simpa [incoherentIfXBranchEnv, Env.update, hb] using hslot)
          simpa [hslotTy, hslotLife] using hxyVar
        rcases incoherentIfXYEnv_lval_facts hxyTyping with
          ⟨_, hpartial, _⟩ | ⟨_, hpartial, _⟩
        · cases hpartial
        · cases hpartial
  | deref lv ih =>
      cases htyping with
      | box hinner =>
          exact False.elim (incoherentIfXBranch_no_box hinner)
      | borrow hinner htargets =>
          rcases ih hinner with ⟨_, _, htargetsEq, _⟩
          subst htargetsEq
          exact False.elim (incoherentIfXBranch_x_targets_not_borrow htargets)

theorem incoherentIfYBranch_borrow_facts {lv : LVal} {mutable : Bool}
    {targets : List LVal} {lifetime : Lifetime} :
    LValTyping incoherentIfYBranchEnv lv
      (.ty (.borrow mutable targets)) lifetime →
    lv = .var "b" ∧ mutable = false ∧ targets = [.var "y"] ∧
      lifetime = Lifetime.root := by
  intro htyping
  induction lv generalizing mutable targets lifetime with
  | var name =>
      rcases LValTyping.var_inv htyping with ⟨slot, hslot, hslotTy, hslotLife⟩
      by_cases hb : name = "b"
      · subst hb
        have hslotEq : slot = incoherentIfBYSlot := by
          have hbSlot :
              incoherentIfYBranchEnv.slotAt "b" =
                some incoherentIfBYSlot := by
            simp [incoherentIfYBranchEnv, incoherentIfBYSlot, Env.update]
          exact Option.some.inj (hslot.symm.trans hbSlot)
        subst hslotEq
        simp [incoherentIfBYSlot] at hslotTy hslotLife
        simp [hslotTy, hslotLife]
      · have hxyTyping :
            LValTyping incoherentIfXYEnv (.var name)
              (.ty (.borrow mutable targets)) lifetime := by
          have hxyVar : LValTyping incoherentIfXYEnv (.var name)
              slot.ty slot.lifetime :=
            @LValTyping.var incoherentIfXYEnv name slot (by
            simpa [incoherentIfYBranchEnv, Env.update, hb] using hslot)
          simpa [hslotTy, hslotLife] using hxyVar
        rcases incoherentIfXYEnv_lval_facts hxyTyping with
          ⟨_, hpartial, _⟩ | ⟨_, hpartial, _⟩
        · cases hpartial
        · cases hpartial
  | deref lv ih =>
      cases htyping with
      | box hinner =>
          exact False.elim (incoherentIfYBranch_no_box hinner)
      | borrow hinner htargets =>
          rcases ih hinner with ⟨_, _, htargetsEq, _⟩
          subst htargetsEq
          exact False.elim (incoherentIfYBranch_y_targets_not_borrow htargets)

theorem incoherentIfXY_coherent : Coherent incoherentIfXYEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases incoherentIfXYEnv_lval_facts htyping with
    ⟨_, hpartial, _⟩ | ⟨_, hpartial, _⟩
  · cases hpartial
  · cases hpartial

theorem incoherentIfXBranch_coherent : Coherent incoherentIfXBranchEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases incoherentIfXBranch_borrow_facts htyping with
    ⟨rfl, rfl, rfl, _⟩
  exact ⟨.int, Lifetime.root,
    LValTargetsTyping.singleton incoherentIfXBranch_x_typing⟩

theorem incoherentIfYBranch_coherent : Coherent incoherentIfYBranchEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases incoherentIfYBranch_borrow_facts htyping with
    ⟨rfl, rfl, rfl, _⟩
  exact ⟨.bool, Lifetime.root,
    LValTargetsTyping.singleton incoherentIfYBranch_y_typing⟩

theorem incoherentIf_freshBorrowX_obligations :
    FreshUpdateCoherenceObligations incoherentIfXYEnv "b"
      (.borrow false [.var "x"]) Lifetime.root := by
  constructor
  · intro lv mutable targets borrowLifetime hbase htyping
    rcases incoherentIfXBranch_borrow_facts htyping with
      ⟨hlv, _hmutable, _htargets, _hlifetime⟩
    subst hlv
    simp [LVal.base] at hbase
  · intro lv mutable targets borrowLifetime hbase htyping
    rcases incoherentIfXBranch_borrow_facts htyping with
      ⟨rfl, rfl, rfl, _⟩
    exact ⟨.int, Lifetime.root,
      LValTargetsTyping.singleton incoherentIfXBranch_x_typing⟩

theorem incoherentIf_freshBorrowY_obligations :
    FreshUpdateCoherenceObligations incoherentIfXYEnv "b"
      (.borrow false [.var "y"]) Lifetime.root := by
  constructor
  · intro lv mutable targets borrowLifetime hbase htyping
    rcases incoherentIfYBranch_borrow_facts htyping with
      ⟨hlv, _hmutable, _htargets, _hlifetime⟩
    subst hlv
    simp [LVal.base] at hbase
  · intro lv mutable targets borrowLifetime hbase htyping
    rcases incoherentIfYBranch_borrow_facts htyping with
      ⟨rfl, rfl, rfl, _⟩
    exact ⟨.bool, Lifetime.root,
      LValTargetsTyping.singleton incoherentIfYBranch_y_typing⟩

theorem incoherentIf_xBranch_typing :
    TermTyping incoherentIfXYEnv StoreTyping.empty Lifetime.root
      (.letMut "b" (.borrow false (.var "x"))) .unit
      incoherentIfXBranchEnv := by
  exact TermTyping.declare
    (by simp [Env.fresh, incoherentIfXYEnv, incoherentIfXEnv, Env.update,
      Env.empty])
    (TermTyping.immBorrow incoherentIfXY_x_typing
      (incoherentIfXY_no_readProhibited (.var "x")))
    (by simp [Env.fresh, incoherentIfXYEnv, incoherentIfXEnv, Env.update,
      Env.empty])
    incoherentIf_freshBorrowX_obligations
    rfl

theorem incoherentIf_yBranch_typing :
    TermTyping incoherentIfXYEnv StoreTyping.empty Lifetime.root
      (.letMut "b" (.borrow false (.var "y"))) .unit
      incoherentIfYBranchEnv := by
  exact TermTyping.declare
    (by simp [Env.fresh, incoherentIfXYEnv, incoherentIfXEnv, Env.update,
      Env.empty])
    (TermTyping.immBorrow incoherentIfXY_y_typing
      (incoherentIfXY_no_readProhibited (.var "y")))
    (by simp [Env.fresh, incoherentIfXYEnv, incoherentIfXEnv, Env.update,
      Env.empty])
    incoherentIf_freshBorrowY_obligations
    rfl

theorem incoherentIfJoin_b_typing :
    LValTyping incoherentIfJoinEnv (.var "b")
      (.ty (.borrow false [.var "x", .var "y"])) Lifetime.root := by
  exact @LValTyping.var incoherentIfJoinEnv "b" incoherentIfBJoinSlot (by
    simp [incoherentIfJoinEnv, incoherentIfBJoinSlot, Env.update])

theorem incoherentIfJoin_x_typing :
    LValTyping incoherentIfJoinEnv (.var "x") (.ty .int) Lifetime.root := by
  exact @LValTyping.var incoherentIfJoinEnv "x" incoherentIfIntSlot (by
    simp [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
      incoherentIfIntSlot, incoherentIfBoolSlot, incoherentIfBJoinSlot,
      Env.update])

theorem incoherentIfJoin_y_typing :
    LValTyping incoherentIfJoinEnv (.var "y") (.ty .bool) Lifetime.root := by
  exact @LValTyping.var incoherentIfJoinEnv "y" incoherentIfBoolSlot (by
    simp [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfBoolSlot,
      incoherentIfBJoinSlot, Env.update])

theorem incoherentIfJoin_not_coherent :
    ¬ Coherent incoherentIfJoinEnv := by
  intro hcoherent
  rcases hcoherent (.var "b") false [.var "x", .var "y"] Lifetime.root
      incoherentIfJoin_b_typing with
    ⟨targetTy, targetLifetime, htargets⟩
  cases htargets with
  | cons hhead hrest hunion _hintersection =>
      rcases LValTyping.var_inv hhead with
        ⟨headSlot, hheadSlot, hheadTy, _hheadLifetime⟩
      have hheadSlotEq : headSlot = incoherentIfIntSlot := by
        have hx :
            incoherentIfJoinEnv.slotAt "x" = some incoherentIfIntSlot := by
          simp [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
            incoherentIfIntSlot, incoherentIfBoolSlot, incoherentIfBJoinSlot,
            Env.update]
        exact Option.some.inj (hheadSlot.symm.trans hx)
      subst hheadSlotEq
      simp [incoherentIfIntSlot] at hheadTy
      cases hheadTy
      cases hrest with
      | singleton htail =>
          rcases LValTyping.var_inv htail with
            ⟨tailSlot, htailSlot, htailTy, _htailLifetime⟩
          have htailSlotEq : tailSlot = incoherentIfBoolSlot := by
            have hy :
                incoherentIfJoinEnv.slotAt "y" =
                  some incoherentIfBoolSlot := by
              simp [incoherentIfJoinEnv, incoherentIfXYEnv,
                incoherentIfBoolSlot, incoherentIfBJoinSlot, Env.update]
            exact Option.some.inj (htailSlot.symm.trans hy)
          subst htailSlotEq
          simp [incoherentIfBoolSlot] at htailTy
          cases htailTy
          have hint : PartialTyStrengthens (.ty .int) (.ty targetTy) :=
            hunion.1 (by simp)
          have hbool : PartialTyStrengthens (.ty .bool) (.ty targetTy) :=
            hunion.1 (by simp)
          have htargetInt := PartialTyStrengthens.from_int_inv hint
          have htargetBool := PartialTyStrengthens.from_bool_inv hbool
          rw [htargetInt] at htargetBool
          cases htargetBool
      | cons _ htailRest _ _ =>
          cases htailRest

structure IfTypingPremisesWithoutCoherent
    (env₁ env₂ env₃ env₄ env₅ : Env) (typing : StoreTyping)
    (lifetime : Lifetime) (condition trueBranch falseBranch : Term)
    (trueTy falseTy joinTy : Ty) : Prop where
  conditionTyping :
    TermTyping env₁ typing lifetime condition .bool env₂
  trueTyping :
    TermTyping env₂ typing lifetime trueBranch trueTy env₃
  falseTyping :
    TermTyping env₂ typing lifetime falseBranch falseTy env₄
  typeJoin :
    PartialTyJoin (.ty trueTy) (.ty falseTy) (.ty joinTy)
  envJoin :
    EnvJoin env₃ env₄ env₅
  sameShapeTrue :
    EnvJoinSameShape env₃ env₅
  sameShapeFalse :
    EnvJoinSameShape env₄ env₅
  resultWellFormed :
    WellFormedTy env₅ joinTy lifetime
  linearizable :
    Linearizable env₅
  borrowSafe :
    BorrowSafeEnv env₅
  resultBorrowSafe :
    TyBorrowSafeAgainstEnv env₅ joinTy

theorem incoherentIf_borrow_append_strengthens {mutable : Bool}
    {leftTargets rightTargets : List LVal} {joined : PartialTy}
    (hleft : PartialTyStrengthens (.ty (.borrow mutable leftTargets)) joined)
    (hright : PartialTyStrengthens (.ty (.borrow mutable rightTargets)) joined) :
    PartialTyStrengthens (.ty (.borrow mutable (leftTargets ++ rightTargets)))
      joined := by
  cases hleft with
  | reflex =>
      have hsubRight := PartialTyStrengthens.borrow_subset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hmem
        · exact hsubRight hmem)
  | borrow hsubLeft =>
      have hsubRight := PartialTyStrengthens.borrow_subset hright
      exact PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem)
  | intoUndef hinner =>
      rcases PartialTyStrengthens.from_borrow_inv hinner with
        ⟨targetTargets, htargetEq, hsubLeft⟩
      cases htargetEq
      have hsubRight : rightTargets ⊆ targetTargets := by
        cases hright with
        | intoUndef hinner' => exact PartialTyStrengthens.borrow_subset hinner'
      exact PartialTyStrengthens.intoUndef (PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem))

theorem incoherentIfXBranch_le_join :
    EnvStrengthens incoherentIfXBranchEnv incoherentIfJoinEnv := by
  intro name
  by_cases hb : name = "b"
  · subst hb
    rw [show incoherentIfXBranchEnv.slotAt "b" = some incoherentIfBXSlot by
        simp [incoherentIfXBranchEnv, incoherentIfBXSlot, Env.update],
      show incoherentIfJoinEnv.slotAt "b" = some incoherentIfBJoinSlot by
        simp [incoherentIfJoinEnv, incoherentIfBJoinSlot, Env.update]]
    refine ⟨rfl, PartialTyStrengthens.borrow ?_⟩
    intro target htarget
    simp at htarget
    subst htarget
    simp
  · by_cases hy : name = "y"
    · subst hy
      rw [show incoherentIfXBranchEnv.slotAt "y" =
            some incoherentIfBoolSlot by
          simp [incoherentIfXBranchEnv, incoherentIfXYEnv,
            incoherentIfBoolSlot, incoherentIfBXSlot, Env.update],
        show incoherentIfJoinEnv.slotAt "y" = some incoherentIfBoolSlot by
          simp [incoherentIfJoinEnv, incoherentIfXYEnv,
            incoherentIfBoolSlot, incoherentIfBJoinSlot, Env.update]]
      exact ⟨rfl, PartialTyStrengthens.reflex⟩
    · by_cases hx : name = "x"
      · subst hx
        rw [show incoherentIfXBranchEnv.slotAt "x" =
              some incoherentIfIntSlot by
            simp [incoherentIfXBranchEnv, incoherentIfXYEnv,
              incoherentIfXEnv, incoherentIfIntSlot, incoherentIfBoolSlot,
              incoherentIfBXSlot, Env.update],
          show incoherentIfJoinEnv.slotAt "x" = some incoherentIfIntSlot by
            simp [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
              incoherentIfIntSlot, incoherentIfBoolSlot, incoherentIfBJoinSlot,
              Env.update]]
        exact ⟨rfl, PartialTyStrengthens.reflex⟩
      · rw [show incoherentIfXBranchEnv.slotAt name = none by
            simp [incoherentIfXBranchEnv, incoherentIfXYEnv, incoherentIfXEnv,
              Env.update, Env.empty, hb, hy, hx],
          show incoherentIfJoinEnv.slotAt name = none by
            simp [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
              Env.update, Env.empty, hb, hy, hx]]
        trivial

theorem incoherentIfYBranch_le_join :
    EnvStrengthens incoherentIfYBranchEnv incoherentIfJoinEnv := by
  intro name
  by_cases hb : name = "b"
  · subst hb
    rw [show incoherentIfYBranchEnv.slotAt "b" = some incoherentIfBYSlot by
        simp [incoherentIfYBranchEnv, incoherentIfBYSlot, Env.update],
      show incoherentIfJoinEnv.slotAt "b" = some incoherentIfBJoinSlot by
        simp [incoherentIfJoinEnv, incoherentIfBJoinSlot, Env.update]]
    refine ⟨rfl, PartialTyStrengthens.borrow ?_⟩
    intro target htarget
    simp at htarget
    subst htarget
    simp
  · by_cases hy : name = "y"
    · subst hy
      rw [show incoherentIfYBranchEnv.slotAt "y" =
            some incoherentIfBoolSlot by
          simp [incoherentIfYBranchEnv, incoherentIfXYEnv,
            incoherentIfBoolSlot, incoherentIfBYSlot, Env.update],
        show incoherentIfJoinEnv.slotAt "y" = some incoherentIfBoolSlot by
          simp [incoherentIfJoinEnv, incoherentIfXYEnv,
            incoherentIfBoolSlot, incoherentIfBJoinSlot, Env.update]]
      exact ⟨rfl, PartialTyStrengthens.reflex⟩
    · by_cases hx : name = "x"
      · subst hx
        rw [show incoherentIfYBranchEnv.slotAt "x" =
              some incoherentIfIntSlot by
            simp [incoherentIfYBranchEnv, incoherentIfXYEnv,
              incoherentIfXEnv, incoherentIfIntSlot, incoherentIfBoolSlot,
              incoherentIfBYSlot, Env.update],
          show incoherentIfJoinEnv.slotAt "x" = some incoherentIfIntSlot by
            simp [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
              incoherentIfIntSlot, incoherentIfBoolSlot, incoherentIfBJoinSlot,
              Env.update]]
        exact ⟨rfl, PartialTyStrengthens.reflex⟩
      · rw [show incoherentIfYBranchEnv.slotAt name = none by
            simp [incoherentIfYBranchEnv, incoherentIfXYEnv, incoherentIfXEnv,
              Env.update, Env.empty, hb, hy, hx],
          show incoherentIfJoinEnv.slotAt name = none by
            simp [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
              Env.update, Env.empty, hb, hy, hx]]
        trivial

theorem incoherentIfJoin_least {env' : Env}
    (hxBranch : EnvStrengthens incoherentIfXBranchEnv env')
    (hyBranch : EnvStrengthens incoherentIfYBranchEnv env') :
    EnvStrengthens incoherentIfJoinEnv env' := by
  intro name
  by_cases hb : name = "b"
  · subst hb
    rcases EnvStrengthens.slot_forward hxBranch (show
        incoherentIfXBranchEnv.slotAt "b" = some incoherentIfBXSlot by
          simp [incoherentIfXBranchEnv, incoherentIfBXSlot, Env.update]) with
      ⟨slotX, hslotX, hlife, hstrX⟩
    rcases EnvStrengthens.slot_forward hyBranch (show
        incoherentIfYBranchEnv.slotAt "b" = some incoherentIfBYSlot by
          simp [incoherentIfYBranchEnv, incoherentIfBYSlot, Env.update]) with
      ⟨slotY, hslotY, _hlifeY, hstrY⟩
    have hslotEq : slotX = slotY := Option.some.inj (hslotX.symm.trans hslotY)
    subst hslotEq
    rw [show incoherentIfJoinEnv.slotAt "b" = some incoherentIfBJoinSlot by
        simp [incoherentIfJoinEnv, incoherentIfBJoinSlot, Env.update], hslotX]
    have hXY : PartialTyStrengthens
        (.ty (.borrow false ([.var "x"] ++ [.var "y"]))) slotX.ty :=
      incoherentIf_borrow_append_strengthens hstrX hstrY
    exact ⟨hlife, by simpa [incoherentIfBJoinSlot] using hXY⟩
  · by_cases hy : name = "y"
    · subst hy
      rcases EnvStrengthens.slot_forward hxBranch (show
          incoherentIfXBranchEnv.slotAt "y" = some incoherentIfBoolSlot by
            simp [incoherentIfXBranchEnv, incoherentIfXYEnv,
              incoherentIfBoolSlot, incoherentIfBXSlot, Env.update]) with
        ⟨slot, hslot, hlife, hstr⟩
      rw [show incoherentIfJoinEnv.slotAt "y" = some incoherentIfBoolSlot by
          simp [incoherentIfJoinEnv, incoherentIfXYEnv,
            incoherentIfBoolSlot, incoherentIfBJoinSlot, Env.update], hslot]
      exact ⟨hlife, hstr⟩
    · by_cases hx : name = "x"
      · subst hx
        rcases EnvStrengthens.slot_forward hxBranch (show
            incoherentIfXBranchEnv.slotAt "x" = some incoherentIfIntSlot by
              simp [incoherentIfXBranchEnv, incoherentIfXYEnv,
                incoherentIfXEnv, incoherentIfIntSlot, incoherentIfBoolSlot,
                incoherentIfBXSlot, Env.update]) with
          ⟨slot, hslot, hlife, hstr⟩
        rw [show incoherentIfJoinEnv.slotAt "x" = some incoherentIfIntSlot by
            simp [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
              incoherentIfIntSlot, incoherentIfBoolSlot, incoherentIfBJoinSlot,
              Env.update], hslot]
        exact ⟨hlife, hstr⟩
      · have hbranchNone : incoherentIfXBranchEnv.slotAt name = none := by
          simp [incoherentIfXBranchEnv, incoherentIfXYEnv, incoherentIfXEnv,
            Env.update, Env.empty, hb, hy, hx]
        have hjoinNone : incoherentIfJoinEnv.slotAt name = none := by
          simp [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
            Env.update, Env.empty, hb, hy, hx]
        have h := hxBranch name
        rw [hbranchNone] at h
        rw [hjoinNone]
        cases henvSlot : env'.slotAt name with
        | none => trivial
        | some envSlot =>
            rw [henvSlot] at h
            cases h

theorem incoherentIf_envJoin :
    EnvJoin incoherentIfXBranchEnv incoherentIfYBranchEnv
      incoherentIfJoinEnv := by
  constructor
  · intro env henv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at henv
    rcases henv with rfl | rfl
    · exact incoherentIfXBranch_le_join
    · exact incoherentIfYBranch_le_join
  · intro env' henv'
    exact incoherentIfJoin_least
      (henv' incoherentIfXBranchEnv (by simp))
      (henv' incoherentIfYBranchEnv (by simp))

theorem incoherentIfXBranch_join_sameShape :
    EnvJoinSameShape incoherentIfXBranchEnv incoherentIfJoinEnv := by
  intro name branchSlot joinSlot hbranch hjoin
  by_cases hb : name = "b"
  · subst hb
    have hbranchTy : branchSlot.ty = .ty (.borrow false [.var "x"]) := by
      simpa [incoherentIfXBranchEnv, incoherentIfBXSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
    have hjoinTy : joinSlot.ty = .ty (.borrow false [.var "x", .var "y"]) := by
      simpa [incoherentIfJoinEnv, incoherentIfBJoinSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
    simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
  · by_cases hy : name = "y"
    · subst hy
      have hbranchTy : branchSlot.ty = .ty .bool := by
        simpa [incoherentIfXBranchEnv, incoherentIfXYEnv,
          incoherentIfBoolSlot, incoherentIfBXSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
      have hjoinTy : joinSlot.ty = .ty .bool := by
        simpa [incoherentIfJoinEnv, incoherentIfXYEnv,
          incoherentIfBoolSlot, incoherentIfBJoinSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
      simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
    · by_cases hx : name = "x"
      · subst hx
        have hbranchTy : branchSlot.ty = .ty .int := by
          simpa [incoherentIfXBranchEnv, incoherentIfXYEnv, incoherentIfXEnv,
            incoherentIfIntSlot, incoherentIfBoolSlot, incoherentIfBXSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
        have hjoinTy : joinSlot.ty = .ty .int := by
          simpa [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
            incoherentIfIntSlot, incoherentIfBoolSlot, incoherentIfBJoinSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
        simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
      · have hnone : incoherentIfXBranchEnv.slotAt name = none := by
          simp [incoherentIfXBranchEnv, incoherentIfXYEnv, incoherentIfXEnv,
            Env.update, Env.empty, hb, hy, hx]
        rw [hbranch] at hnone
        cases hnone

theorem incoherentIfYBranch_join_sameShape :
    EnvJoinSameShape incoherentIfYBranchEnv incoherentIfJoinEnv := by
  intro name branchSlot joinSlot hbranch hjoin
  by_cases hb : name = "b"
  · subst hb
    have hbranchTy : branchSlot.ty = .ty (.borrow false [.var "y"]) := by
      simpa [incoherentIfYBranchEnv, incoherentIfBYSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
    have hjoinTy : joinSlot.ty = .ty (.borrow false [.var "x", .var "y"]) := by
      simpa [incoherentIfJoinEnv, incoherentIfBJoinSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
    simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
  · by_cases hy : name = "y"
    · subst hy
      have hbranchTy : branchSlot.ty = .ty .bool := by
        simpa [incoherentIfYBranchEnv, incoherentIfXYEnv,
          incoherentIfBoolSlot, incoherentIfBYSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
      have hjoinTy : joinSlot.ty = .ty .bool := by
        simpa [incoherentIfJoinEnv, incoherentIfXYEnv,
          incoherentIfBoolSlot, incoherentIfBJoinSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
      simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
    · by_cases hx : name = "x"
      · subst hx
        have hbranchTy : branchSlot.ty = .ty .int := by
          simpa [incoherentIfYBranchEnv, incoherentIfXYEnv, incoherentIfXEnv,
            incoherentIfIntSlot, incoherentIfBoolSlot, incoherentIfBYSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hbranch).symm
        have hjoinTy : joinSlot.ty = .ty .int := by
          simpa [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
            incoherentIfIntSlot, incoherentIfBoolSlot, incoherentIfBJoinSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hjoin).symm
        simp [hbranchTy, hjoinTy, PartialTy.sameShape, Ty.sameShape]
      · have hnone : incoherentIfYBranchEnv.slotAt name = none := by
          simp [incoherentIfYBranchEnv, incoherentIfXYEnv, incoherentIfXEnv,
            Env.update, Env.empty, hb, hy, hx]
        rw [hbranch] at hnone
        cases hnone

theorem incoherentIfJoin_linearizable : Linearizable incoherentIfJoinEnv := by
  refine ⟨fun name => if name = "b" then 1 else 0, ?_⟩
  intro root slot hslot v hv
  by_cases hb : root = "b"
  · subst hb
    have hslotTy : slot.ty = .ty (.borrow false [.var "x", .var "y"]) := by
      simpa [incoherentIfJoinEnv, incoherentIfBJoinSlot, Env.update] using
        (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
    rw [hslotTy] at hv
    simp [PartialTy.vars, Ty.vars, LVal.base] at hv
    rcases hv with rfl | rfl <;> simp
  · by_cases hy : root = "y"
    · subst hy
      have hslotTy : slot.ty = .ty .bool := by
        simpa [incoherentIfJoinEnv, incoherentIfXYEnv,
          incoherentIfBoolSlot, incoherentIfBJoinSlot, Env.update] using
          (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
      rw [hslotTy] at hv
      simp [PartialTy.vars, Ty.vars] at hv
    · by_cases hx : root = "x"
      · subst hx
        have hslotTy : slot.ty = .ty .int := by
          simpa [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
            incoherentIfIntSlot, incoherentIfBoolSlot, incoherentIfBJoinSlot,
            Env.update] using
            (congrArg (fun slotOpt => Option.map EnvSlot.ty slotOpt) hslot).symm
        rw [hslotTy] at hv
        simp [PartialTy.vars, Ty.vars] at hv
      · have hnone : incoherentIfJoinEnv.slotAt root = none := by
          simp [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
            Env.update, Env.empty, hb, hy, hx]
        rw [hslot] at hnone
        cases hnone

theorem incoherentIfJoin_no_mutable_contains {root : Name}
    {targets : List LVal} :
    ¬ incoherentIfJoinEnv ⊢ root ↝ (.borrow true targets) := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  by_cases hb : root = "b"
  · subst hb
    have hslotEq : slot = incoherentIfBJoinSlot := by
      have hbSlot :
          incoherentIfJoinEnv.slotAt "b" = some incoherentIfBJoinSlot := by
        simp [incoherentIfJoinEnv, incoherentIfBJoinSlot, Env.update]
      exact Option.some.inj (hslot.symm.trans hbSlot)
    subst hslotEq
    simp [incoherentIfBJoinSlot] at hcontainsTy
    cases hcontainsTy
  · by_cases hy : root = "y"
    · subst hy
      have hslotEq : slot = incoherentIfBoolSlot := by
        have hySlot :
            incoherentIfJoinEnv.slotAt "y" = some incoherentIfBoolSlot := by
          simp [incoherentIfJoinEnv, incoherentIfXYEnv,
            incoherentIfBoolSlot, incoherentIfBJoinSlot, Env.update]
        exact Option.some.inj (hslot.symm.trans hySlot)
      subst hslotEq
      simp [incoherentIfBoolSlot] at hcontainsTy
      cases hcontainsTy
    · by_cases hx : root = "x"
      · subst hx
        have hslotEq : slot = incoherentIfIntSlot := by
          have hxSlot :
              incoherentIfJoinEnv.slotAt "x" = some incoherentIfIntSlot := by
            simp [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
              incoherentIfIntSlot, incoherentIfBoolSlot, incoherentIfBJoinSlot,
              Env.update]
          exact Option.some.inj (hslot.symm.trans hxSlot)
        subst hslotEq
        simp [incoherentIfIntSlot] at hcontainsTy
        cases hcontainsTy
      · have hnone : incoherentIfJoinEnv.slotAt root = none := by
          simp [incoherentIfJoinEnv, incoherentIfXYEnv, incoherentIfXEnv,
            Env.update, Env.empty, hb, hy, hx]
        rw [hslot] at hnone
        cases hnone

theorem incoherentIfJoin_borrowSafe : BorrowSafeEnv incoherentIfJoinEnv := by
  intro x y mutable targetsMutable targetsOther targetMutable targetOther
    hcontainsMutable _hcontainsOther _htargetMutable _htargetOther _hconflict
  exact False.elim (incoherentIfJoin_no_mutable_contains hcontainsMutable)

theorem tyBorrowSafeAgainstEnv_unit {env : Env} :
    TyBorrowSafeAgainstEnv env .unit := by
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther
      hcontains _hcontainsOther _htargetMutable _htargetOther _hconflict
    cases hcontains
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      _hcontainsMutable hcontains _htargetMutable _htargetOther _hconflict
    cases hcontains

theorem incoherentIf_join_of_coherent_sameShape_counterexample :
    Coherent incoherentIfXYEnv ∧
      Coherent incoherentIfXBranchEnv ∧
      Coherent incoherentIfYBranchEnv ∧
      EnvJoin incoherentIfXBranchEnv incoherentIfYBranchEnv
        incoherentIfJoinEnv ∧
      EnvJoinSameShape incoherentIfXBranchEnv incoherentIfJoinEnv ∧
      EnvJoinSameShape incoherentIfYBranchEnv incoherentIfJoinEnv ∧
      Linearizable incoherentIfJoinEnv ∧
      BorrowSafeEnv incoherentIfJoinEnv ∧
      ¬ Coherent incoherentIfJoinEnv :=
  ⟨incoherentIfXY_coherent,
    incoherentIfXBranch_coherent,
    incoherentIfYBranch_coherent,
    incoherentIf_envJoin,
    incoherentIfXBranch_join_sameShape,
    incoherentIfYBranch_join_sameShape,
    incoherentIfJoin_linearizable,
    incoherentIfJoin_borrowSafe,
    incoherentIfJoin_not_coherent⟩

theorem incoherentIf_without_coherent_premise :
    IfTypingPremisesWithoutCoherent
      incoherentIfXYEnv incoherentIfXYEnv
      incoherentIfXBranchEnv incoherentIfYBranchEnv incoherentIfJoinEnv
      StoreTyping.empty Lifetime.root
      (.val (.bool true))
      (.letMut "b" (.borrow false (.var "x")))
      (.letMut "b" (.borrow false (.var "y")))
      .unit .unit .unit := by
  exact {
    conditionTyping := TermTyping.const ValueTyping.bool
    trueTyping := incoherentIf_xBranch_typing
    falseTyping := incoherentIf_yBranch_typing
    typeJoin := PartialTyJoin.self (.ty .unit)
    envJoin := incoherentIf_envJoin
    sameShapeTrue := incoherentIfXBranch_join_sameShape
    sameShapeFalse := incoherentIfYBranch_join_sameShape
    resultWellFormed := WellFormedTy.unit
    linearizable := incoherentIfJoin_linearizable
    borrowSafe := incoherentIfJoin_borrowSafe
    resultBorrowSafe := tyBorrowSafeAgainstEnv_unit
  }

theorem incoherentIf_term_typing_without_coherent_premise :
    TermTyping incoherentIfXYEnv StoreTyping.empty Lifetime.root
      incoherentIfTerm .unit incoherentIfJoinEnv := by
  exact TermTyping.ite
    (TermTyping.const ValueTyping.bool)
    incoherentIf_xBranch_typing
    incoherentIf_yBranch_typing
    (PartialTyJoin.self (.ty .unit))
    incoherentIf_envJoin
    incoherentIfXBranch_join_sameShape
    incoherentIfYBranch_join_sameShape
    WellFormedTy.unit
    incoherentIfJoin_linearizable
    incoherentIfJoin_borrowSafe
    tyBorrowSafeAgainstEnv_unit

theorem rawIncoherentIf_unscoped_reachable_counterexample :
    TermListTyping Env.empty StoreTyping.empty Lifetime.root
        incoherentIfPrefix .unit incoherentIfXYEnv ∧
      IfTypingPremisesWithoutCoherent
        incoherentIfXYEnv incoherentIfXYEnv
        incoherentIfXBranchEnv incoherentIfYBranchEnv incoherentIfJoinEnv
        StoreTyping.empty Lifetime.root
        (.val (.bool true))
        (.letMut "b" (.borrow false (.var "x")))
        (.letMut "b" (.borrow false (.var "y")))
        .unit .unit .unit ∧
      ¬ Coherent incoherentIfJoinEnv :=
  ⟨incoherentIfPrefix_typing, incoherentIf_without_coherent_premise,
    incoherentIfJoin_not_coherent⟩

theorem rawIncoherentIf_unscoped_reachable_termTyping_counterexample :
    SourceTerm incoherentIfTerm ∧
      ¬ BlockScopedSourceTerm incoherentIfTerm ∧
      TermListTyping Env.empty StoreTyping.empty Lifetime.root
        incoherentIfPrefix .unit incoherentIfXYEnv ∧
      TermTyping incoherentIfXYEnv StoreTyping.empty Lifetime.root
        incoherentIfTerm .unit incoherentIfJoinEnv ∧
      ¬ Coherent incoherentIfJoinEnv :=
  ⟨incoherentIfTerm_sourceTerm, incoherentIfTerm_not_blockScopedSourceTerm,
    incoherentIfPrefix_typing, incoherentIf_term_typing_without_coherent_premise,
    incoherentIfJoin_not_coherent⟩

def rawIncoherentIfProgram : List Term :=
  incoherentIfPrefix ++ [incoherentIfTerm]

theorem rawIncoherentIf_unscoped_reachable_termListTyping_counterexample :
    TermListTyping Env.empty StoreTyping.empty Lifetime.root
        rawIncoherentIfProgram .unit incoherentIfJoinEnv ∧
      ¬ BlockScopedSourceTerm incoherentIfTerm ∧
      ¬ Coherent incoherentIfJoinEnv := by
  constructor
  · unfold rawIncoherentIfProgram incoherentIfPrefix
    exact TermListTyping.cons incoherentIf_declareX_typing
      (TermListTyping.cons incoherentIf_declareY_typing
        (TermListTyping.singleton
          incoherentIf_term_typing_without_coherent_premise))
  · exact ⟨incoherentIfTerm_not_blockScopedSourceTerm,
      incoherentIfJoin_not_coherent⟩

theorem not_all_empty_initial_termList_typings_coherent :
    ¬ (∀ {terms ty env},
      TermListTyping Env.empty StoreTyping.empty Lifetime.root terms ty env →
      Coherent env) := by
  intro hallCoherent
  rcases rawIncoherentIf_unscoped_reachable_termListTyping_counterexample with
    ⟨htyping, _hunscoped, hnotCoherent⟩
  exact hnotCoherent (hallCoherent htyping)

/-! ### The minimal RHS-target obligation rejects the multi-target fan-out
counterexample.

The broad `ContainedBorrowsWellFormed` of the assign result was load-bearing
exactly because writing through a multi-target borrow `&mut[x,z]` whose targets
have different lifetimes fans the RHS into a longer-lived slot, and the lhs's
`targetLifetime` is only the *intersection* of the targets' lifetimes.  The
minimal replacement `EnvWriteRhsTargetsWellFormed` is UNSATISFIABLE in exactly
that situation: here the result slot `x @ [0]` holds a borrow of `w @ [0,0]`
(the RHS edge), and `[0,0]` does not outlive `[0]`, so the obligation fails — it
rejects the dangling write, confirming the replacement is sound, not merely
derivable. -/
def fanoutRejectSlotX : EnvSlot :=
  { ty := .ty (.borrow true [.var "w"]), lifetime := ([0] : Lifetime) }

def fanoutRejectSlotW : EnvSlot :=
  { ty := .ty .int, lifetime := ([0, 0] : Lifetime) }

def fanoutRejectEnv : Env :=
  { slotAt := fun n =>
      if n = "x" then some fanoutRejectSlotX
      else if n = "w" then some fanoutRejectSlotW else none }

example :
    ¬ EnvWriteRhsTargetsWellFormed fanoutRejectEnv (.borrow true [.var "w"]) := by
  intro h
  obtain ⟨tTy, tLf, htyp, hle, _⟩ :=
    h "x" fanoutRejectSlotX true [.var "w"] (.var "w")
      (by simp [fanoutRejectEnv])
      (PartialTyContains.here)
      (by simp)
      ⟨true, [.var "w"], PartialTyContains.here, by simp⟩
  rcases LValTyping.var_inv htyp with ⟨slot, hslot, _hty, hlf⟩
  simp only [fanoutRejectEnv, if_neg (by decide : ("w" : Name) ≠ "x")] at hslot
  injection hslot with hslotEq
  subst hslotEq
  rw [← hlf] at hle
  simp [fanoutRejectSlotW, fanoutRejectSlotX, LifetimeOutlives,
    Core.Lifetime.contains] at hle

end Paper
end LwRust
