import LwRust.Extractor.CompleteProgram
import LwRust.Paper.Soundness.Helpers.BorrowWellFormed

/-!
Completeness of the canonical lifetime annotation pass.

The source language used by the extractor has no block-lifetime annotations.
`RawTerm.Annotates` describes any structural insertion of such annotations,
while `RawTerm.annotate` picks the canonical child lifetime at every block.
This file proves that if some structural annotation typechecks, then the
canonical annotation typechecks as well.
-/

namespace ConservativeExtractor

open LwRust.Core
open LwRust.Paper

namespace AnnotationCompleteness

/-- The canonical representative for an arbitrary lifetime is the zero path at
the same lexical depth. -/
def canonicalLifetime (lifetime : Lifetime) : Lifetime :=
  { path := List.replicate lifetime.path.length 0 }

@[simp] theorem canonicalLifetime_root :
    canonicalLifetime LwRust.Core.Lifetime.root = LwRust.Core.Lifetime.root := by
  rfl

theorem canonicalLifetime_child {parent child : Lifetime} :
    LifetimeChild parent child →
    canonicalLifetime child =
      RawTerm.childLifetime (canonicalLifetime parent) := by
  rintro ⟨label, hpath⟩
  cases parent with
  | mk parentPath =>
      cases child with
      | mk childPath =>
          simp [canonicalLifetime, RawTerm.childLifetime] at hpath ⊢
          rw [hpath, List.length_append]
          simp
          rw [← List.replicate_append_replicate]
          rfl

theorem childLifetime_child (lifetime : Lifetime) :
    LifetimeChild lifetime (RawTerm.childLifetime lifetime) := by
  exact ⟨0, rfl⟩

private theorem canonicalLifetime_outlives {outer inner : Lifetime} :
    outer ≤ inner → canonicalLifetime outer ≤ canonicalLifetime inner := by
  intro houtlives
  have hprefix : outer.path <+: inner.path := by
    exact List.isPrefixOf_iff_prefix.mp
      (by simpa [LifetimeOutlives, LwRust.Core.Lifetime.contains] using houtlives)
  have hlength : outer.path.length ≤ inner.path.length :=
    hprefix.length_le
  rcases Nat.exists_eq_add_of_le hlength with ⟨suffixLength, hinnerLength⟩
  have hprefixCanonical :
      List.replicate outer.path.length 0 <+:
        List.replicate inner.path.length 0 := by
    refine ⟨List.replicate suffixLength 0, ?_⟩
    rw [hinnerLength]
    rw [List.replicate_append_replicate]
  exact List.isPrefixOf_iff_prefix.mpr hprefixCanonical

private theorem lifetime_eq_of_outlives_of_canonical_eq
    {left right : Lifetime} :
    left ≤ right →
    canonicalLifetime left = canonicalLifetime right →
    left = right := by
  intro houtlives hcanonical
  have hprefix : left.path <+: right.path := by
    exact List.isPrefixOf_iff_prefix.mp
      (by simpa [LifetimeOutlives, LwRust.Core.Lifetime.contains] using houtlives)
  have hlength : left.path.length = right.path.length := by
    have hpath := congrArg Lifetime.path hcanonical
    have hlengthPath := congrArg List.length hpath
    simpa [canonicalLifetime] using hlengthPath
  have hpathEq : left.path = right.path :=
    hprefix.eq_of_length hlength
  cases left
  cases right
  simp at hpathEq ⊢
  exact hpathEq

private theorem lifetime_outlives_parent_of_outlives_child_ne
    {lifetime parent child : Lifetime} :
    LifetimeChild parent child →
    lifetime ≤ child →
    lifetime ≠ child →
    lifetime ≤ parent := by
  rintro ⟨label, hchildPath⟩ houtlives hne
  have hprefix : lifetime.path <+: child.path := by
    exact List.isPrefixOf_iff_prefix.mp
      (by simpa [LifetimeOutlives, LwRust.Core.Lifetime.contains] using houtlives)
  have hlengthNe : lifetime.path.length ≠ child.path.length := by
    intro hlength
    exact hne (by
      cases lifetime
      cases child
      simp at hlength hprefix ⊢
      exact hprefix.eq_of_length hlength)
  have hlengthLt : lifetime.path.length < child.path.length :=
    lt_of_le_of_ne hprefix.length_le hlengthNe
  have hchildLength :
      child.path.length = parent.path.length + 1 := by
    rw [hchildPath, List.length_append]
    simp
  have hlengthParent : lifetime.path.length ≤ parent.path.length := by
    rw [hchildLength] at hlengthLt
    exact Nat.lt_succ_iff.mp hlengthLt
  let n := lifetime.path.length
  rcases hprefix with ⟨suffix, hsuffix⟩
  have htakeChild :
      List.take n child.path = lifetime.path := by
    rw [← hsuffix]
    exact List.take_left
  have htakeParent :
      List.take n parent.path = lifetime.path := by
    calc
      List.take n parent.path =
          List.take n (parent.path ++ [label]) :=
            (List.take_append_of_le_length (by simpa [n] using hlengthParent)).symm
      _ = List.take n child.path := by rw [← hchildPath]
      _ = lifetime.path := htakeChild
  exact List.isPrefixOf_iff_prefix.mpr
    ⟨List.drop n parent.path, by
      calc
        lifetime.path ++ List.drop n parent.path =
            List.take n parent.path ++ List.drop n parent.path := by
              rw [htakeParent]
        _ = parent.path := List.take_append_drop n parent.path⟩

private theorem EnvSlotsOutlive.dropLifetime_to_parent {env : Env}
    {parent child : Lifetime} :
    LifetimeChild parent child →
    EnvSlotsOutlive env child →
    EnvSlotsOutlive (env.dropLifetime child) parent := by
  intro hchild hslots x slot hslot
  rcases Env.dropLifetime_slotAt_eq_some.mp hslot with ⟨horig, hne⟩
  exact lifetime_outlives_parent_of_outlives_child_ne hchild
    (hslots x slot horig) hne

/--
Environments are canonicalized pointwise: domains and partial types are
unchanged, and every slot lifetime is replaced by its canonical depth
representative.
-/
def EnvCanon (source target : Env) : Prop :=
  ∀ x,
    match source.slotAt x with
    | none => target.slotAt x = none
    | some slot =>
        target.slotAt x =
          some { slot with lifetime := canonicalLifetime slot.lifetime }

theorem EnvCanon.refl_empty :
    EnvCanon Env.empty Env.empty := by
  intro x
  rfl

theorem EnvSlotsOutlive.empty (lifetime : Lifetime) :
    EnvSlotsOutlive Env.empty lifetime := by
  intro x slot hslot
  simp [Env.empty] at hslot

theorem EnvCanon.fresh {source target : Env} {x : Name} :
    EnvCanon source target →
    source.fresh x →
    target.fresh x := by
  intro hcanon hfresh
  have htarget := hcanon x
  rw [show source.slotAt x = none from hfresh] at htarget
  exact htarget

theorem EnvCanon.update {source target : Env} {x : Name} {slot : EnvSlot} :
    EnvCanon source target →
    EnvCanon (source.update x slot)
      (target.update x { slot with lifetime := canonicalLifetime slot.lifetime }) := by
  intro hcanon y
  by_cases hy : y = x
  · subst hy
    simp [Env.update]
  · simp [Env.update, hy, hcanon y]

theorem EnvCanon.dropLifetime {source target : Env} {lifetime : Lifetime} :
    EnvCanon source target →
    EnvSlotsOutlive source lifetime →
    EnvCanon (source.dropLifetime lifetime)
      (target.dropLifetime (canonicalLifetime lifetime)) := by
  intro hcanon hslots x
  unfold Env.dropLifetime
  cases hsource : source.slotAt x with
  | none =>
      have htarget : target.slotAt x = none := by
        simpa [hsource] using hcanon x
      simp [hsource, htarget]
  | some slot =>
      have htarget :
          target.slotAt x =
            some { slot with lifetime := canonicalLifetime slot.lifetime } := by
        simpa [hsource] using hcanon x
      by_cases hlifetime : slot.lifetime = lifetime
      · subst hlifetime
        simp [hsource, htarget]
      · have hcanonNe :
            canonicalLifetime slot.lifetime ≠ canonicalLifetime lifetime := by
          intro hcanonical
          exact hlifetime
            (lifetime_eq_of_outlives_of_canonical_eq
              (hslots x slot hsource) hcanonical)
        simp [hsource, htarget, hlifetime, hcanonNe]

theorem EnvCanon.contains_of_source {source target : Env}
    {x : Name} {ty : Ty} :
    EnvCanon source target →
    source ⊢ x ↝ ty →
    target ⊢ x ↝ ty := by
  intro hcanon hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  refine ⟨{ slot with lifetime := canonicalLifetime slot.lifetime }, ?_, ?_⟩
  · simpa [hslot] using hcanon x
  · simpa using hcontainsTy

theorem EnvCanon.contains_of_target {source target : Env}
    {x : Name} {ty : Ty} :
    EnvCanon source target →
    target ⊢ x ↝ ty →
    source ⊢ x ↝ ty := by
  intro hcanon hcontains
  rcases hcontains with ⟨targetSlot, htargetSlot, hcontainsTy⟩
  cases hsource : source.slotAt x with
  | none =>
      have htarget : target.slotAt x = none := by
        simpa [hsource] using hcanon x
      rw [htarget] at htargetSlot
      cases htargetSlot
  | some sourceSlot =>
      have htarget :
          target.slotAt x =
            some { sourceSlot with
              lifetime := canonicalLifetime sourceSlot.lifetime } := by
        simpa [hsource] using hcanon x
      have hslotEq :
          targetSlot =
            { sourceSlot with
              lifetime := canonicalLifetime sourceSlot.lifetime } :=
        Option.some.inj (htargetSlot.symm.trans htarget)
      subst hslotEq
      exact ⟨sourceSlot, hsource, by simpa using hcontainsTy⟩

theorem LValBaseOutlives.canonical {source target : Env}
    {lv : LVal} {lifetime : Lifetime} :
    EnvCanon source target →
    LValBaseOutlives source lv lifetime →
    LValBaseOutlives target lv (canonicalLifetime lifetime) := by
  intro hcanon hbase
  rcases hbase with ⟨slot, hslot, houtlives⟩
  refine ⟨{ slot with lifetime := canonicalLifetime slot.lifetime }, ?_, ?_⟩
  · simpa [hslot] using hcanon (LVal.base lv)
  · exact canonicalLifetime_outlives houtlives

theorem LValTyping.canonical {source target : Env}
    (hcanon : EnvCanon source target) :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping source lv partialTy lifetime →
      LValTyping target lv partialTy (canonicalLifetime lifetime) := by
  intro lv partialTy lifetime htyping
  induction htyping with
  | var hslot =>
      rename_i x slot
      exact LValTyping.var (by simpa [hslot] using hcanon x)
  | «box» _ ih =>
      exact LValTyping.box ih
  | boxFull _ ih =>
      exact LValTyping.boxFull ih
  | «borrow» _ _ ihBorrow ihTarget =>
      exact LValTyping.borrow ihBorrow ihTarget

theorem Mutable.canonical {source target : Env} {lv : LVal} :
    EnvCanon source target →
    Mutable source lv →
    Mutable target lv := by
  intro hcanon hmutable
  induction hmutable with
  | var hslot =>
      rename_i x slot
      exact Mutable.var (by simpa [hslot] using hcanon x)
  | «box» htyping _ ih =>
      exact Mutable.box (LValTyping.canonical hcanon htyping) ih
  | boxFull htyping _ ih =>
      exact Mutable.boxFull (LValTyping.canonical hcanon htyping) ih
  | «borrow» htyping _ ih =>
      exact Mutable.borrow (LValTyping.canonical hcanon htyping) ih

theorem ReadProhibited.of_canonical {source target : Env} {lv : LVal} :
    EnvCanon source target →
    ReadProhibited target lv →
    ReadProhibited source lv := by
  intro hcanon hread
  rcases hread with ⟨x, borrowTarget, hcontains, hconflict⟩
  exact ⟨x, borrowTarget, EnvCanon.contains_of_target hcanon hcontains, hconflict⟩

theorem WriteProhibited.of_canonical {source target : Env} {lv : LVal} :
    EnvCanon source target →
    WriteProhibited target lv →
    WriteProhibited source lv := by
  intro hcanon hwrite
  cases hwrite with
  | inl hread =>
      exact Or.inl (ReadProhibited.of_canonical hcanon hread)
  | inr hwrite =>
      rcases hwrite with ⟨x, borrowTarget, hcontains, hconflict⟩
      exact Or.inr
        ⟨x, borrowTarget, EnvCanon.contains_of_target hcanon hcontains,
          hconflict⟩

theorem BorrowTargetsWellFormed.canonical {source target : Env}
    {lv : LVal} {lifetime : Lifetime} :
    EnvCanon source target →
    BorrowTargetsWellFormed source lv lifetime →
    BorrowTargetsWellFormed target lv (canonicalLifetime lifetime) := by
  intro hcanon htargets
  cases htargets with
  | intro hmember =>
      rcases hmember with
        ⟨targetTy, targetLifetime, htyping, houtlives, hbase⟩
      exact BorrowTargetsWellFormed.intro
        ⟨targetTy, canonicalLifetime targetLifetime,
          LValTyping.canonical hcanon htyping,
          canonicalLifetime_outlives houtlives,
          LValBaseOutlives.canonical hcanon hbase⟩

theorem WellFormedTy.canonical {source target : Env}
    {ty : Ty} {lifetime : Lifetime} :
    EnvCanon source target →
    WellFormedTy source ty lifetime →
    WellFormedTy target ty (canonicalLifetime lifetime) := by
  intro hcanon hwell
  induction hwell with
  | unit => exact WellFormedTy.unit
  | int => exact WellFormedTy.int
  | «borrow» htargets =>
      exact WellFormedTy.borrow
        (BorrowTargetsWellFormed.canonical hcanon htargets)
  | «box» _ ih =>
      exact WellFormedTy.box ih

theorem ShapeCompatible.canonical {source target : Env}
    {left right : PartialTy} :
    EnvCanon source target →
    ShapeCompatible source left right →
    ShapeCompatible target left right := by
  intro hcanon hshape
  induction hshape with
  | unit => exact ShapeCompatible.unit
  | int => exact ShapeCompatible.int
  | tyBox _ ih => exact ShapeCompatible.tyBox ih
  | «box» _ ih => exact ShapeCompatible.box ih
  | «borrow» hleft hright _ ih =>
      rcases hleft with ⟨leftLifetime, hleftTyping⟩
      rcases hright with ⟨rightLifetime, hrightTyping⟩
      exact ShapeCompatible.borrow
        ⟨canonicalLifetime leftLifetime,
          LValTyping.canonical hcanon hleftTyping⟩
        ⟨canonicalLifetime rightLifetime,
          LValTyping.canonical hcanon hrightTyping⟩
        ih
  | undefLeft _ ih => exact ShapeCompatible.undefLeft ih
  | undefRight _ ih => exact ShapeCompatible.undefRight ih

theorem EnvMove.canonical {source target moved : Env} {lv : LVal} :
    EnvCanon source target →
    EnvMove source lv moved →
    ∃ movedTarget,
      EnvMove target lv movedTarget ∧ EnvCanon moved movedTarget := by
  intro hcanon hmove
  rcases hmove with ⟨slot, struck, hslot, hstrike, hmoved⟩
  subst hmoved
  let targetSlot : EnvSlot :=
    { slot with lifetime := canonicalLifetime slot.lifetime }
  let movedTarget : Env :=
    target.update (LVal.base lv) { targetSlot with ty := struck }
  refine ⟨movedTarget, ?_, ?_⟩
  · refine ⟨targetSlot, struck, ?_, ?_, rfl⟩
    · simpa [targetSlot, hslot] using hcanon (LVal.base lv)
    · simpa [targetSlot] using hstrike
  · intro x
    by_cases hx : x = LVal.base lv
    · subst hx
      simp [Env.update, targetSlot, movedTarget]
    · cases hsource : source.slotAt x with
      | none =>
          have htarget : target.slotAt x = none := by
            simpa [hsource] using hcanon x
          simp [Env.update, hx, hsource, htarget, targetSlot, movedTarget]
      | some sourceSlot =>
          have htarget :
              target.slotAt x =
                some { sourceSlot with
                  lifetime := canonicalLifetime sourceSlot.lifetime } := by
            simpa [hsource] using hcanon x
          simp [Env.update, hx, hsource, htarget, targetSlot, movedTarget]

theorem EnvWrite.envSlotsOutlive :
    ∀ {env result : Env} {lv : LVal} {ty : Ty} {current : Lifetime},
      EnvWrite env lv ty result →
      EnvSlotsOutlive env current →
      EnvSlotsOutlive result current := by
  intro env result lv ty current hwrite hslots
  exact EnvWrite.rec
    (motive_1 := fun _path _old _ty result _updated _ =>
      EnvSlotsOutlive result current)
    (motive_2 := fun _lv _ty result _ =>
      EnvSlotsOutlive result current)
    (by intro old ty; exact hslots)
    (by
      intro env₂ path inner updatedInner ty hupdate ih
      exact ih)
    (by
      intro env₂ path inner updatedInner ty hupdate ih
      exact ih)
    (by
      intro env₂ path target ty hwrite ih
      exact ih)
    (by
      intro env₂ lv slot ty updatedTy hslot _hupdate ih x resultSlot hresultSlot
      by_cases hx : x = LVal.base lv
      · subst hx
        have hslotEq : resultSlot = { slot with ty := updatedTy } := by
          have hsome :
              some { slot with ty := updatedTy } = some resultSlot := by
            simpa [Env.update] using hresultSlot
          exact (Option.some.inj hsome).symm
        subst hslotEq
        simpa using hslots (LVal.base lv) slot hslot
      · have henv₂Slot : env₂.slotAt x = some resultSlot := by
          simpa [Env.update, hx] using hresultSlot
        exact ih x resultSlot henv₂Slot)
    hwrite

theorem EnvWrite.canonical :
    ∀ {source target result : Env} {lv : LVal} {ty : Ty},
      EnvCanon source target →
      EnvWrite source lv ty result →
      ∃ resultTarget,
        EnvWrite target lv ty resultTarget ∧ EnvCanon result resultTarget := by
  intro source target result lv ty hcanon hwrite
  exact EnvWrite.rec
    (motive_1 := fun path old ty result updated hupdate =>
      ∀ {target : Env}, EnvCanon source target →
        ∃ resultTarget,
          UpdateAtPath target path old ty resultTarget updated ∧
            EnvCanon result resultTarget)
    (motive_2 := fun lv ty result hwrite =>
      ∀ {target : Env}, EnvCanon source target →
        ∃ resultTarget,
          EnvWrite target lv ty resultTarget ∧ EnvCanon result resultTarget)
    (by
      intro old ty target hcanon
      exact ⟨target, UpdateAtPath.strong, hcanon⟩)
    (by
      intro env₂ path inner updatedInner ty hupdate ih target hcanon
      rcases ih hcanon with
        ⟨resultTarget, hupdateTarget, hresultCanon⟩
      exact ⟨resultTarget, UpdateAtPath.box hupdateTarget, hresultCanon⟩)
    (by
      intro env₂ path inner updatedInner ty hupdate ih target hcanon
      rcases ih hcanon with
        ⟨resultTarget, hupdateTarget, hresultCanon⟩
      exact ⟨resultTarget, UpdateAtPath.boxFull hupdateTarget, hresultCanon⟩)
    (by
      intro env₂ path targetLv ty hwrite ih target hcanon
      rcases ih hcanon with
        ⟨resultTarget, hwriteTarget, hresultCanon⟩
      exact ⟨resultTarget, UpdateAtPath.mutBorrow hwriteTarget, hresultCanon⟩)
    (by
      intro env₂ lv sourceSlot ty updatedTy hslot hupdate ih target hcanon
      rcases ih hcanon with
        ⟨env₂Target, hupdateTarget, henv₂Canon⟩
      let targetSlot : EnvSlot :=
        { sourceSlot with
          lifetime := canonicalLifetime sourceSlot.lifetime }
      let resultTarget : Env :=
        env₂Target.update (LVal.base lv) { targetSlot with ty := updatedTy }
      refine ⟨resultTarget, ?_, ?_⟩
      · refine EnvWrite.intro ?_ hupdateTarget
        simpa [targetSlot, hslot] using hcanon (LVal.base lv)
      · simpa [targetSlot, resultTarget] using
          EnvCanon.update (source := env₂) (target := env₂Target)
            (x := LVal.base lv) (slot := { sourceSlot with ty := updatedTy })
            henv₂Canon)
    hwrite hcanon

theorem EnvMove.envSlotsOutlive {env moved : Env} {lv : LVal}
    {current : Lifetime} :
    EnvMove env lv moved →
    EnvSlotsOutlive env current →
    EnvSlotsOutlive moved current := by
  intro hmove hslots
  rcases hmove with ⟨slot, struck, hslot, _hstrike, hmoved⟩
  subst hmoved
  intro x movedSlot hmovedSlot
  by_cases hx : x = LVal.base lv
  · subst hx
    have hmovedSlotEq : movedSlot = { slot with ty := struck } := by
      have hsome : some { slot with ty := struck } = some movedSlot := by
        simpa [Env.update] using hmovedSlot
      exact (Option.some.inj hsome).symm
    subst hmovedSlotEq
    simpa using hslots (LVal.base lv) slot hslot
  · have hsourceSlot : env.slotAt x = some movedSlot := by
      simpa [Env.update, hx] using hmovedSlot
    exact hslots x movedSlot hsourceSlot

mutual

theorem canonical_of_annotates
    :
    ∀ {raw : RawTerm} {annotated : Term},
    RawTerm.Annotates raw annotated →
    ∀ (env envCanon : Env) (typing : StoreTyping)
      (lifetime : Lifetime) (ty : Ty) (env₂ : Env),
      EnvCanon env envCanon →
      EnvSlotsOutlive env lifetime →
      TermTyping env typing lifetime annotated ty env₂ →
      ∃ env₂Canon,
        TermTyping envCanon typing (canonicalLifetime lifetime)
          (RawTerm.annotate (canonicalLifetime lifetime) raw) ty env₂Canon ∧
        EnvCanon env₂ env₂Canon ∧
        EnvSlotsOutlive env₂ lifetime
  | _, _, RawTerm.Annotates.block hterms => by
      rename_i terms blockLifetime annotatedTerms
      intro env envCanon typing lifetime ty env₂ henvCanon hslots htyping
      cases htyping with
      | «block» hchild htermList hwellTy hdrop =>
          subst hdrop
          have hinnerSlots : EnvSlotsOutlive env _ :=
            EnvSlotsOutlive.weaken hslots (LifetimeChild.outlives hchild)
          rcases canonicalList_of_annotates hterms env envCanon typing _ ty _
              henvCanon hinnerSlots htermList with
            ⟨env₂Canon, htermsCanon, henv₂Canon, hslots₂⟩
          have hchildCanon := canonicalLifetime_child hchild
          have hwellCanon :
              WellFormedTy env₂Canon ty (canonicalLifetime lifetime) :=
            WellFormedTy.canonical henv₂Canon hwellTy
          refine ⟨env₂Canon.dropLifetime (canonicalLifetime blockLifetime), ?_, ?_, ?_⟩
          · rw [hchildCanon] at htermsCanon
            rw [hchildCanon]
            exact TermTyping.block
              (childLifetime_child (canonicalLifetime lifetime))
              htermsCanon hwellCanon rfl
          · exact EnvCanon.dropLifetime henv₂Canon hslots₂
          · exact EnvSlotsOutlive.dropLifetime_to_parent hchild hslots₂
  | _, _, RawTerm.Annotates.letMut hinit => by
      rename_i x initialiser annotatedInitialiser
      intro env envCanon typing lifetime ty env₂ henvCanon hslots htyping
      cases htyping with
      | declare hterm hfresh hupdate =>
          rename_i envInit initTy
          subst hupdate
          rcases canonical_of_annotates hinit env envCanon typing lifetime initTy _
              henvCanon hslots hterm with
            ⟨env₂Canon, htermCanon, henv₂Canon, hslots₂⟩
          let declaredSlot : EnvSlot :=
            EnvSlot.mk (PartialTy.ty initTy) (canonicalLifetime lifetime)
          refine ⟨env₂Canon.update x declaredSlot, ?_, ?_, ?_⟩
          · exact TermTyping.declare htermCanon
              (EnvCanon.fresh henv₂Canon hfresh) rfl
          · exact EnvCanon.update henv₂Canon
          · exact EnvSlotsOutlive.update_current hslots₂
  | _, _, RawTerm.Annotates.assign hrhs => by
      intro env envCanon typing lifetime ty env₂ henvCanon hslots htyping
      cases htyping with
      | assign hterm hlv hshape hwellTy hwrite hnotWrite =>
          rcases canonical_of_annotates hrhs env envCanon typing lifetime _ _
              henvCanon hslots hterm with
            ⟨env₂Canon, htermCanon, henv₂Canon, hslots₂⟩
          rcases EnvWrite.canonical henv₂Canon hwrite with
            ⟨env₃Canon, hwriteCanon, henv₃Canon⟩
          refine ⟨env₃Canon, ?_, henv₃Canon, ?_⟩
          · exact TermTyping.assign htermCanon
              (LValTyping.canonical henv₂Canon hlv)
              (ShapeCompatible.canonical henv₂Canon hshape)
              (WellFormedTy.canonical henv₂Canon hwellTy)
              hwriteCanon
              (by
                intro hwriteProhibited
                exact hnotWrite
                  (WriteProhibited.of_canonical henv₃Canon hwriteProhibited))
          · exact EnvWrite.envSlotsOutlive hwrite hslots₂
  | _, _, RawTerm.Annotates.box hoperand => by
      intro env envCanon typing lifetime ty env₂ henvCanon hslots htyping
      cases htyping with
      | «box» hterm =>
          rcases canonical_of_annotates hoperand env envCanon typing lifetime _ _
              henvCanon hslots hterm with
            ⟨env₂Canon, htermCanon, henv₂Canon, hslots₂⟩
          exact ⟨env₂Canon, TermTyping.box htermCanon, henv₂Canon, hslots₂⟩
  | _, _, RawTerm.Annotates.borrow => by
      intro env envCanon typing lifetime ty env₂ henvCanon hslots htyping
      cases htyping with
      | mutBorrow hlv hmutable hnotWrite =>
          exact ⟨envCanon,
            TermTyping.mutBorrow
              (LValTyping.canonical henvCanon hlv)
              (Mutable.canonical henvCanon hmutable)
              (by
                intro hwriteProhibited
                exact hnotWrite
                  (WriteProhibited.of_canonical henvCanon hwriteProhibited)),
            henvCanon, hslots⟩
      | immBorrow hlv hnotRead =>
          exact ⟨envCanon,
            TermTyping.immBorrow
              (LValTyping.canonical henvCanon hlv)
              (by
                intro hreadProhibited
                exact hnotRead
                  (ReadProhibited.of_canonical henvCanon hreadProhibited)),
            henvCanon, hslots⟩
  | _, _, RawTerm.Annotates.move => by
      intro env envCanon typing lifetime ty env₂ henvCanon hslots htyping
      cases htyping with
      | «move» hlv hnotWrite hmove =>
          rcases EnvMove.canonical henvCanon hmove with
            ⟨movedCanon, hmoveCanon, hmovedCanon⟩
          exact ⟨movedCanon,
            TermTyping.move
              (LValTyping.canonical henvCanon hlv)
              (by
                intro hwriteProhibited
                exact hnotWrite
                  (WriteProhibited.of_canonical henvCanon hwriteProhibited))
              hmoveCanon,
            hmovedCanon,
            EnvMove.envSlotsOutlive hmove hslots⟩
  | _, _, RawTerm.Annotates.copy => by
      intro env envCanon typing lifetime ty env₂ henvCanon hslots htyping
      cases htyping with
      | «copy» hlv hcopy hnotRead =>
          exact ⟨envCanon,
            TermTyping.copy
              (LValTyping.canonical henvCanon hlv)
              hcopy
              (by
                intro hreadProhibited
                exact hnotRead
                  (ReadProhibited.of_canonical henvCanon hreadProhibited)),
            henvCanon, hslots⟩
  | _, _, RawTerm.Annotates.val => by
      intro env envCanon typing lifetime ty env₂ henvCanon hslots htyping
      cases htyping with
      | const hvalue =>
          exact ⟨envCanon, TermTyping.const hvalue, henvCanon, hslots⟩

theorem canonicalList_of_annotates
    :
    ∀ {raws : List RawTerm} {annotated : List Term},
    RawTerm.AnnotatesList raws annotated →
    ∀ (env envCanon : Env) (typing : StoreTyping)
      (lifetime : Lifetime) (ty : Ty) (env₂ : Env),
      EnvCanon env envCanon →
      EnvSlotsOutlive env lifetime →
      TermListTyping env typing lifetime annotated ty env₂ →
      ∃ env₂Canon,
        TermListTyping envCanon typing (canonicalLifetime lifetime)
          (RawTerm.annotateList (canonicalLifetime lifetime) raws) ty env₂Canon ∧
        EnvCanon env₂ env₂Canon ∧
        EnvSlotsOutlive env₂ lifetime
  | _, _, RawTerm.AnnotatesList.nil => by
      intro env envCanon typing lifetime ty env₂ henvCanon hslots htyping
      cases htyping
  | _, _, RawTerm.AnnotatesList.cons hhead htail => by
      intro env envCanon typing lifetime ty env₂ henvCanon hslots htyping
      cases htyping with
      | singleton hterm =>
          cases htail
          rcases canonical_of_annotates hhead env envCanon typing lifetime _ _
              henvCanon hslots hterm with
            ⟨env₂Canon, htermCanon, henv₂Canon, hslots₂⟩
          exact ⟨env₂Canon,
            by
              simpa [RawTerm.annotateList] using
                TermListTyping.singleton htermCanon,
            henv₂Canon, hslots₂⟩
      | cons hterm hrest =>
          rcases canonical_of_annotates hhead env envCanon typing lifetime _ _
              henvCanon hslots hterm with
            ⟨envHeadCanon, htermCanon, henvHeadCanon, hslotsHead⟩
          rcases canonicalList_of_annotates htail _ envHeadCanon typing
              lifetime ty _ henvHeadCanon hslotsHead hrest with
            ⟨env₂Canon, hrestCanon, henv₂Canon, hslots₂⟩
          exact ⟨env₂Canon,
            by
              simpa [RawTerm.annotateList] using
                TermListTyping.cons htermCanon hrestCanon,
            henv₂Canon, hslots₂⟩

end

theorem canonical_program_typing_of_annotates
    {raw : RawProgram} {annotated : Program} {ty : Ty} {env : Env} :
    RawTerm.AnnotatesProgram raw annotated →
    TermTyping Env.empty StoreTyping.empty LwRust.Core.Lifetime.root
      annotated ty env →
    ∃ envCanon,
      TermTyping Env.empty StoreTyping.empty LwRust.Core.Lifetime.root
        (RawTerm.annotateProgram raw) ty envCanon := by
  intro hannot htyping
  rcases canonical_of_annotates hannot Env.empty Env.empty StoreTyping.empty
      LwRust.Core.Lifetime.root ty env EnvCanon.refl_empty
      (EnvSlotsOutlive.empty LwRust.Core.Lifetime.root) htyping with
    ⟨envCanon, hcanonTyping, _henvCanon, _hslots⟩
  exact ⟨envCanon, by
    simpa [RawTerm.annotateProgram, canonicalLifetime_root] using hcanonTyping⟩

end AnnotationCompleteness

end ConservativeExtractor
