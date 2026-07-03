import LwRust.Paper.Examples.Operational
import LwRust.Paper.Soundness.Helpers.Frame
import LwRust.Paper.Soundness.InitialStates

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
                                        hwrite _hnoStale _hranked _hcoherent
                                        _hrhsTargets hnotWrite =>
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
