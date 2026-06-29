import LwRust.Extractor.RelaxedPreservationCases

/-!
# Frontier lemmas for relaxed preservation

The relaxed `T-If` cases can be proved without `BorrowSafeEnv` on the joined
environment.  The next obligation is continuation code typed under the joined
approximation: runtime safety is available for an exact selected-branch
environment, but the tail's typing premises are stated for the approximation.

This file packages that frontier as a checked reduction.  If an assignment
redex can be transported from the approximate environment to the exact runtime
environment, path-sensitive preservation follows from the existing strict
assignment-preservation engine.
-/

namespace LwRust
namespace Paper

open Core

/--
Assignment typing/runtime facts re-established for the exact runtime
environment, plus the map from the exact output back to the approximate output.

For `lhs = .deref source`, producing this package is the hard part: the
approximate environment may contain a joined multi-target borrow, while the
exact environment contains only the branch-selected targets.  The existing
selected-target graph lemmas
`EnvWrite.runtime_selected_lval_map` and
`EnvWrite.runtime_selected_spine_map` are the tools that should construct the
`outMap` after the write.
-/
structure ExactAssignTransport (lifetime : Lifetime) (lhs : LVal)
    (rhsTy : Ty) (exactIn exactOut approxOut : Env)
    (oldTy : PartialTy) (targetLifetime rhsWellLifetime : Lifetime) :
    Prop where
  lval : LValTyping exactIn lhs oldTy targetLifetime
  shape : ShapeCompatible exactIn oldTy (.ty rhsTy)
  wellTy : WellFormedTy exactIn rhsTy rhsWellLifetime
  write : EnvWrite 0 exactIn lhs rhsTy exactOut
  ranked :
    ∃ φ, LinearizedBy φ exactIn ∧
      EnvWriteRhsBorrowTargetsBelow φ exactOut rhsTy
  notWrite : ¬ WriteProhibited exactOut lhs
  wellOut : WellFormedEnv exactOut lifetime
  borrowOut : BorrowSafeEnv exactOut
  outMap : EnvSameShapeStrengthening exactOut approxOut

/--
The remaining typed assignment continuation obligation.

After the RHS has evaluated, the runtime path provides a selected exact input
environment and selected exact RHS type.  A proof of this hook rebuilds the
assignment typing/write facts for that exact path and maps the exact output back
to the approximate continuation output.
-/
def TypedAssignTransportHook (lifetime : Lifetime) (lhs : LVal)
    (approxRhsTy : Ty) (approxRhs approxOut : Env) : Prop :=
  ∀ {storeV storeAfter : ProgramStore} {value finalValueV : Value},
    PathSensitiveTypedTerminalStateSafe storeV lifetime value approxRhs
      approxRhsTy →
    ValidRuntimeState storeV (.assign lhs (.val value)) →
    Step storeV lifetime (.assign lhs (.val value)) storeAfter
      (.val finalValueV) →
    ∀ exactIn exactRhsTy,
      WellFormedEnv exactIn lifetime →
      BorrowSafeEnv exactIn →
      storeV ∼ₛ exactIn →
      EnvSameShapeStrengthening exactIn approxRhs →
      PartialTyStrengthens (.ty exactRhsTy) (.ty approxRhsTy) →
      ValidValue storeV value exactRhsTy →
      WellFormedTy exactIn exactRhsTy lifetime →
      TyBorrowSafeAgainstEnv exactIn exactRhsTy →
      ∃ exactOut oldTy targetLifetime rhsWellLifetime,
        ExactAssignTransport lifetime lhs exactRhsTy exactIn exactOut
          approxOut oldTy targetLifetime rhsWellLifetime

/--
Build the exact assignment package once the genuinely exact assignment facts
and the exact-output-to-approx-output map are known.

Ranking and `¬WriteProhibited` are transported back from the approximate output;
they are not separate exact-side obligations.
-/
theorem ExactAssignTransport.of_core_and_approx_guards
    {lifetime : Lifetime} {lhs : LVal} {rhsTy : Ty}
    {exactIn exactOut approxIn approxOut : Env}
    {oldTy : PartialTy} {targetLifetime rhsWellLifetime : Lifetime}
    {φ : Name → Nat} :
    EnvSameShapeStrengthening exactIn approxIn →
    LinearizedBy φ approxIn →
    EnvWriteRhsBorrowTargetsBelow φ approxOut rhsTy →
    ¬ WriteProhibited approxOut lhs →
    LValTyping exactIn lhs oldTy targetLifetime →
    ShapeCompatible exactIn oldTy (.ty rhsTy) →
    WellFormedTy exactIn rhsTy rhsWellLifetime →
    EnvWrite 0 exactIn lhs rhsTy exactOut →
    WellFormedEnv exactOut lifetime →
    BorrowSafeEnv exactOut →
    EnvSameShapeStrengthening exactOut approxOut →
    ExactAssignTransport lifetime lhs rhsTy exactIn exactOut approxOut
      oldTy targetLifetime rhsWellLifetime := by
  intro hmapIn hφApprox hbelowApprox hnotWriteApprox hlval hshape hwellTy
    hwrite hwellOut hborrowOut houtMap
  have hrankedExact :
      ∃ exactφ, LinearizedBy exactφ exactIn ∧
        EnvWriteRhsBorrowTargetsBelow exactφ exactOut rhsTy :=
    ⟨φ,
      LinearizedBy.of_sameShapeStrengthening hmapIn hφApprox,
      EnvWriteRhsBorrowTargetsBelow.of_sameShapeStrengthening
        houtMap hbelowApprox⟩
  have hnotWriteExact : ¬ WriteProhibited exactOut lhs := by
    intro hwriteExact
    exact hnotWriteApprox
      (WriteProhibited.of_sameShapeStrengthening houtMap hwriteExact)
  exact
    { lval := hlval
      shape := hshape
      wellTy := hwellTy
      write := hwrite
      ranked := hrankedExact
      notWrite := hnotWriteExact
      wellOut := hwellOut
      borrowOut := hborrowOut
      outMap := houtMap }

/--
Variant of `of_core_and_approx_guards` that derives exact output
well-formedness from the local write-preservation ingredients.

This splits the broad `WellFormedEnv exactOut` obligation into the two parts
that still genuinely need exact-output evidence: coherence and RHS-target
well-formedness.  CBWF, slot lifetimes, and linearizability are derived from the
exact input and the transported rank/write-prohibition guards.
-/
theorem ExactAssignTransport.of_core_and_approx_guards_wellFormedParts
    {lifetime : Lifetime} {lhs : LVal} {rhsTy : Ty}
    {exactIn exactOut approxIn approxOut : Env}
    {oldTy : PartialTy} {targetLifetime rhsWellLifetime : Lifetime}
    {φ : Name → Nat} :
    WellFormedEnv exactIn lifetime →
    EnvSameShapeStrengthening exactIn approxIn →
    LinearizedBy φ approxIn →
    EnvWriteRhsBorrowTargetsBelow φ approxOut rhsTy →
    ¬ WriteProhibited approxOut lhs →
    LValTyping exactIn lhs oldTy targetLifetime →
    ShapeCompatible exactIn oldTy (.ty rhsTy) →
    WellFormedTy exactIn rhsTy rhsWellLifetime →
    EnvWrite 0 exactIn lhs rhsTy exactOut →
    Coherent exactOut →
    EnvWriteRhsTargetsWellFormed exactOut rhsTy →
    BorrowSafeEnv exactOut →
    EnvSameShapeStrengthening exactOut approxOut →
    ExactAssignTransport lifetime lhs rhsTy exactIn exactOut approxOut
      oldTy targetLifetime rhsWellLifetime := by
  intro hwellIn hmapIn hφApprox hbelowApprox hnotWriteApprox hlval hshape
    hwellTy hwrite hcohOut hrhsTargetsOut hborrowOut houtMap
  have hφExactIn : LinearizedBy φ exactIn :=
    LinearizedBy.of_sameShapeStrengthening hmapIn hφApprox
  have hbelowExact :
      EnvWriteRhsBorrowTargetsBelow φ exactOut rhsTy :=
    EnvWriteRhsBorrowTargetsBelow.of_sameShapeStrengthening
      houtMap hbelowApprox
  have hlinOutBy : LinearizedBy φ exactOut :=
    EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
      hwrite hφExactIn hbelowExact
  have hnotWriteExact : ¬ WriteProhibited exactOut lhs := by
    intro hwriteExact
    exact hnotWriteApprox
      (WriteProhibited.of_sameShapeStrengthening houtMap hwriteExact)
  have hwellOut : WellFormedEnv exactOut lifetime :=
    ⟨containedBorrowsWellFormed_assign hwellIn.1 hcohOut
        (Linearizable.of_linearizedBy hlinOutBy) hrhsTargetsOut
        hwrite hnotWriteExact,
      EnvSlotsOutlive.of_lifetimesPreserved hwellIn.2.1
        (EnvWrite.lifetimesPreserved hwrite),
      hcohOut,
      Linearizable.of_linearizedBy hlinOutBy⟩
  exact
    ExactAssignTransport.of_core_and_approx_guards
      hmapIn hφApprox hbelowApprox hnotWriteApprox hlval hshape hwellTy
      hwrite hwellOut hborrowOut houtMap

/--
Selected variable-location writes already have the needed output map.

The exact environment may be a selected branch and `approxIn` may be the joined
post-`if` approximation.  Once runtime lookup identifies the single variable
slot actually written, updating that selected slot in the exact environment
strengthens to the fan-out write result computed in the approximation.
-/
theorem EnvWrite.selected_lval_exact_update_to_approx_result_map
    {store : ProgramStore} {exactIn approxIn approxOut : Env}
    {current lifetime : Lifetime} {lv : LVal}
    {lvTy rhsTy approxSelectedSlotTy : Ty} {selectedName : Name}
    {exactSelectedSlot approxSelectedSlot : EnvSlot} {rank : Nat}
    {φ : Name → Nat} :
    EnvSameShapeStrengthening exactIn approxIn →
    exactIn.slotAt selectedName = some exactSelectedSlot →
    approxIn.slotAt selectedName = some approxSelectedSlot →
    LinearizedBy φ approxIn →
    WellFormedEnv approxIn current →
    store ∼ₛ approxIn →
    StoreOwnerTargetsHeap store →
    LValTyping approxIn lv (.ty lvTy) lifetime →
    store.loc lv = some (VariableProjection selectedName) →
    approxSelectedSlot.ty = .ty approxSelectedSlotTy →
    EnvWrite rank approxIn lv rhsTy approxOut →
    EnvSameShapeStrengthening
      (exactIn.update selectedName
        { exactSelectedSlot with ty := .ty rhsTy })
      approxOut := by
  intro hmapExactApprox hexactSelected happroxSelected hφ hwellApprox
    hsafeApprox hheap hlv hloc hselectedTy hwriteApprox
  have hselectedUpdateMap :
      EnvSameShapeStrengthening
        (exactIn.update selectedName
          { exactSelectedSlot with ty := .ty rhsTy })
        (approxIn.update selectedName
          { approxSelectedSlot with ty := .ty rhsTy }) :=
    EnvSameShapeStrengthening.update_both_same_ty hmapExactApprox
      hexactSelected happroxSelected
  have happroxSelectedToOut :
      EnvSameShapeStrengthening
        (approxIn.update selectedName
          { approxSelectedSlot with ty := .ty rhsTy })
        approxOut :=
    EnvWrite.runtime_selected_lval_map hφ hwellApprox hsafeApprox hheap
      hlv hloc happroxSelected hselectedTy hwriteApprox
  exact EnvSameShapeStrengthening.trans hselectedUpdateMap happroxSelectedToOut

/--
Typed variant of `EnvWrite.selected_lval_exact_update_to_approx_result_map`.

The selected exact branch may type the assigned value with a stronger type than
the joined approximation used by the continuation.  Updating the exact selected
slot with the stronger type still strengthens to the approximate write output.
-/
theorem EnvWrite.selected_lval_exact_update_to_approx_result_map_ty_strengthening
    {store : ProgramStore} {exactIn approxIn approxOut : Env}
    {current lifetime : Lifetime} {lv : LVal}
    {lvTy exactRhsTy approxRhsTy approxSelectedSlotTy : Ty}
    {selectedName : Name}
    {exactSelectedSlot approxSelectedSlot : EnvSlot} {rank : Nat}
    {φ : Name → Nat} :
    EnvSameShapeStrengthening exactIn approxIn →
    exactIn.slotAt selectedName = some exactSelectedSlot →
    approxIn.slotAt selectedName = some approxSelectedSlot →
    PartialTyStrengthens (.ty exactRhsTy) (.ty approxRhsTy) →
    LinearizedBy φ approxIn →
    WellFormedEnv approxIn current →
    store ∼ₛ approxIn →
    StoreOwnerTargetsHeap store →
    LValTyping approxIn lv (.ty lvTy) lifetime →
    store.loc lv = some (VariableProjection selectedName) →
    approxSelectedSlot.ty = .ty approxSelectedSlotTy →
    EnvWrite rank approxIn lv approxRhsTy approxOut →
    EnvSameShapeStrengthening
      (exactIn.update selectedName
        { exactSelectedSlot with ty := .ty exactRhsTy })
      approxOut := by
  intro hmapExactApprox hexactSelected happroxSelected hstrength hφ
    hwellApprox hsafeApprox hheap hlv hloc hselectedTy hwriteApprox
  have hselectedUpdateMap :
      EnvSameShapeStrengthening
        (exactIn.update selectedName
          { exactSelectedSlot with ty := .ty exactRhsTy })
        (approxIn.update selectedName
          { approxSelectedSlot with ty := .ty approxRhsTy }) :=
    EnvSameShapeStrengthening.update_both_ty_strengthening hmapExactApprox
      hexactSelected happroxSelected hstrength
  have happroxSelectedToOut :
      EnvSameShapeStrengthening
        (approxIn.update selectedName
          { approxSelectedSlot with ty := .ty approxRhsTy })
        approxOut :=
    EnvWrite.runtime_selected_lval_map hφ hwellApprox hsafeApprox hheap
      hlv hloc happroxSelected hselectedTy hwriteApprox
  exact EnvSameShapeStrengthening.trans hselectedUpdateMap happroxSelectedToOut

/--
Heap-location writes have the analogous selected-output map.  Runtime owner
resolution identifies one owner root and spine; updating that exact owner root
with the same strong leaf replacement strengthens to the approximate fan-out
write result.
-/
theorem EnvWrite.selected_spine_exact_update_to_approx_result_map
    {store : ProgramStore} {exactIn approxIn approxOut : Env}
    {current lifetime : Lifetime} {lv : LVal} {lvTy rhsTy : Ty}
    {address : Nat} {xRoot : Name}
    {exactRootSlot approxRootSlot : EnvSlot}
    {rootSlot leafSlot : StoreSlot} {spinePath : List Unit} {leafTy : Ty}
    {rank : Nat} {φ : Name → Nat} :
    EnvSameShapeStrengthening exactIn approxIn →
    exactIn.slotAt xRoot = some exactRootSlot →
    approxIn.slotAt xRoot = some approxRootSlot →
    LinearizedBy φ approxIn →
    WellFormedEnv approxIn current →
    store ∼ₛ approxIn →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    StoreOwnerSpine store (VariableProjection xRoot) rootSlot
      approxRootSlot.ty spinePath (.heap address) leafSlot (.ty leafTy) →
    spinePath ≠ [] →
    LValTyping approxIn lv (.ty lvTy) lifetime →
    store.loc lv = some (.heap address) →
    EnvWrite rank approxIn lv rhsTy approxOut →
    EnvSameShapeStrengthening
      (exactIn.update xRoot
        { exactRootSlot with
            ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
              rhsTy })
      approxOut := by
  intro hmapExactApprox hexactRoot happroxRoot hφ hwellApprox hsafeApprox
    hvalidStore hheap hspine hspineNonempty hlv hloc hwriteApprox
  have hrootUpdateMap :
      EnvSameShapeStrengthening
        (exactIn.update xRoot
          { exactRootSlot with
              ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
                rhsTy })
        (approxIn.update xRoot
          { approxRootSlot with
              ty := PartialTy.strongLeafUpdate approxRootSlot.ty spinePath
                rhsTy }) :=
    EnvSameShapeStrengthening.update_both_strongLeafUpdate hmapExactApprox
      hexactRoot happroxRoot
  have happroxRootToOut :
      EnvSameShapeStrengthening
        (approxIn.update xRoot
          { approxRootSlot with
              ty := PartialTy.strongLeafUpdate approxRootSlot.ty spinePath
                rhsTy })
        approxOut :=
    EnvWrite.runtime_selected_spine_map hφ hwellApprox hsafeApprox
      hvalidStore hheap happroxRoot hspine hspineNonempty hlv hloc
      hwriteApprox
  exact EnvSameShapeStrengthening.trans hrootUpdateMap happroxRootToOut

/--
Typed variant of `EnvWrite.selected_spine_exact_update_to_approx_result_map`.
The exact owner spine can receive a stronger RHS type than the approximate
fan-out write.
-/
theorem EnvWrite.selected_spine_exact_update_to_approx_result_map_ty_strengthening
    {store : ProgramStore} {exactIn approxIn approxOut : Env}
    {current lifetime : Lifetime} {lv : LVal}
    {lvTy exactRhsTy approxRhsTy : Ty}
    {address : Nat} {xRoot : Name}
    {exactRootSlot approxRootSlot : EnvSlot}
    {rootSlot leafSlot : StoreSlot} {spinePath : List Unit} {leafTy : Ty}
    {rank : Nat} {φ : Name → Nat} :
    EnvSameShapeStrengthening exactIn approxIn →
    exactIn.slotAt xRoot = some exactRootSlot →
    approxIn.slotAt xRoot = some approxRootSlot →
    PartialTyStrengthens (.ty exactRhsTy) (.ty approxRhsTy) →
    LinearizedBy φ approxIn →
    WellFormedEnv approxIn current →
    store ∼ₛ approxIn →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    StoreOwnerSpine store (VariableProjection xRoot) rootSlot
      approxRootSlot.ty spinePath (.heap address) leafSlot (.ty leafTy) →
    spinePath ≠ [] →
    LValTyping approxIn lv (.ty lvTy) lifetime →
    store.loc lv = some (.heap address) →
    EnvWrite rank approxIn lv approxRhsTy approxOut →
    EnvSameShapeStrengthening
      (exactIn.update xRoot
        { exactRootSlot with
            ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
              exactRhsTy })
      approxOut := by
  intro hmapExactApprox hexactRoot happroxRoot hstrength hφ hwellApprox
    hsafeApprox hvalidStore hheap hspine hspineNonempty hlv hloc
    hwriteApprox
  have hrootUpdateMap :
      EnvSameShapeStrengthening
        (exactIn.update xRoot
          { exactRootSlot with
              ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
                exactRhsTy })
        (approxIn.update xRoot
          { approxRootSlot with
              ty := PartialTy.strongLeafUpdate approxRootSlot.ty spinePath
                approxRhsTy }) :=
    EnvSameShapeStrengthening.update_both_strongLeafUpdate_ty_strengthening
      hmapExactApprox hexactRoot happroxRoot hstrength
  have happroxRootToOut :
      EnvSameShapeStrengthening
        (approxIn.update xRoot
          { approxRootSlot with
              ty := PartialTy.strongLeafUpdate approxRootSlot.ty spinePath
                approxRhsTy })
        approxOut :=
    EnvWrite.runtime_selected_spine_map hφ hwellApprox hsafeApprox
      hvalidStore hheap happroxRoot hspine hspineNonempty hlv hloc
      hwriteApprox
  exact EnvSameShapeStrengthening.trans hrootUpdateMap happroxRootToOut

/--
Direct variable assignment transport, factored to expose only the remaining
exact-side obligations.

The selected runtime/output map supplies `outMap`, and approximate RHS
borrow-safety supplies `borrowOut` for the exact selected update.  The theorem
still asks explicitly for exact shape/RHS well-formedness plus the two exact
output well-formedness ingredients not derived here: coherence and RHS-target
well-formedness.
-/
theorem ExactAssignTransport.var_of_approx_selected
    {store : ProgramStore} {lifetime rhsWellLifetime : Lifetime}
    {x : Name} {rhsTy approxSelectedSlotTy : Ty}
    {exactIn approxIn approxOut : Env}
    {exactSlot approxSlot : EnvSlot} {φ : Name → Nat} :
    EnvSameShapeStrengthening exactIn approxIn →
    exactIn.slotAt x = some exactSlot →
    approxIn.slotAt x = some approxSlot →
    approxSlot.ty = .ty approxSelectedSlotTy →
    LinearizedBy φ approxIn →
    WellFormedEnv approxIn lifetime →
    store ∼ₛ approxIn →
    StoreOwnerTargetsHeap store →
    EnvWrite 0 approxIn (.var x) rhsTy approxOut →
    EnvWriteRhsBorrowTargetsBelow φ approxOut rhsTy →
    WellFormedEnv exactIn lifetime →
    BorrowSafeEnv exactIn →
    TyBorrowSafeAgainstEnv approxIn rhsTy →
    ShapeCompatible exactIn exactSlot.ty (.ty rhsTy) →
    WellFormedTy exactIn rhsTy rhsWellLifetime →
    ¬ WriteProhibited approxOut (.var x) →
    Coherent
      (exactIn.update x { exactSlot with ty := .ty rhsTy }) →
    EnvWriteRhsTargetsWellFormed
      (exactIn.update x { exactSlot with ty := .ty rhsTy }) rhsTy →
    ExactAssignTransport lifetime (.var x) rhsTy exactIn
      (exactIn.update x { exactSlot with ty := .ty rhsTy }) approxOut
      exactSlot.ty exactSlot.lifetime rhsWellLifetime := by
  intro hmapExactApprox hexactSlot happroxSlot happroxSlotTy hφApprox
    hwellApprox hsafeApprox hheap hwriteApprox hbelowApprox hwellExact
    hborrowExact hsafeTyApprox hshapeExact hwellTyExact hnotWriteApprox
    hcohOutExact hrhsTargetsOutExact
  have happroxLval :
      LValTyping approxIn (.var x) (.ty approxSelectedSlotTy)
        approxSlot.lifetime := by
    rw [← happroxSlotTy]
    exact LValTyping.var happroxSlot
  have houtMap :
      EnvSameShapeStrengthening
        (exactIn.update x { exactSlot with ty := .ty rhsTy }) approxOut :=
    EnvWrite.selected_lval_exact_update_to_approx_result_map
      hmapExactApprox hexactSlot happroxSlot hφApprox hwellApprox
      hsafeApprox hheap happroxLval
      (by simp [ProgramStore.loc, VariableProjection])
      happroxSlotTy hwriteApprox
  have hborrowOut :
      BorrowSafeEnv
        (exactIn.update x { exactSlot with ty := .ty rhsTy }) :=
    BorrowSafeEnv.update_of_approx_tyBorrowSafe hmapExactApprox hborrowExact
      hsafeTyApprox hexactSlot
  have hwriteExact :
      EnvWrite 0 exactIn (.var x) rhsTy
        (exactIn.update x { exactSlot with ty := .ty rhsTy }) :=
    EnvWrite.intro hexactSlot UpdateAtPath.strong
  exact
    ExactAssignTransport.of_core_and_approx_guards_wellFormedParts
      hwellExact hmapExactApprox hφApprox hbelowApprox hnotWriteApprox
      (LValTyping.var hexactSlot) hshapeExact hwellTyExact hwriteExact
      hcohOutExact hrhsTargetsOutExact hborrowOut houtMap

/--
Typed direct variable assignment transport.

This is the first continuation frontier where the exact runtime branch can use
a stronger RHS type than the joined continuation.  The exact write is performed
with the stronger type and the output is weakened back to the approximate write
result.
-/
theorem ExactAssignTransport.var_of_approx_selected_typed
    {store : ProgramStore} {lifetime rhsWellLifetime : Lifetime}
    {x : Name} {exactRhsTy approxRhsTy approxSelectedSlotTy : Ty}
    {exactIn approxIn approxOut : Env}
    {exactSlot approxSlot : EnvSlot} {φ : Name → Nat} :
    EnvSameShapeStrengthening exactIn approxIn →
    exactIn.slotAt x = some exactSlot →
    approxIn.slotAt x = some approxSlot →
    approxSlot.ty = .ty approxSelectedSlotTy →
    PartialTyStrengthens (.ty exactRhsTy) (.ty approxRhsTy) →
    LinearizedBy φ approxIn →
    WellFormedEnv approxIn lifetime →
    store ∼ₛ approxIn →
    StoreOwnerTargetsHeap store →
    EnvWrite 0 approxIn (.var x) approxRhsTy approxOut →
    EnvWriteRhsBorrowTargetsBelow φ approxOut approxRhsTy →
    WellFormedEnv exactIn lifetime →
    BorrowSafeEnv exactIn →
    TyBorrowSafeAgainstEnv exactIn exactRhsTy →
    ShapeCompatible exactIn exactSlot.ty (.ty exactRhsTy) →
    WellFormedTy exactIn exactRhsTy rhsWellLifetime →
    ¬ WriteProhibited approxOut (.var x) →
    Coherent
      (exactIn.update x { exactSlot with ty := .ty exactRhsTy }) →
    EnvWriteRhsTargetsWellFormed
      (exactIn.update x { exactSlot with ty := .ty exactRhsTy })
      exactRhsTy →
    ExactAssignTransport lifetime (.var x) exactRhsTy exactIn
      (exactIn.update x { exactSlot with ty := .ty exactRhsTy })
      approxOut exactSlot.ty exactSlot.lifetime rhsWellLifetime := by
  intro hmapExactApprox hexactSlot happroxSlot happroxSlotTy hstrength
    hφApprox hwellApprox hsafeApprox hheap hwriteApprox hbelowApprox
    hwellExact hborrowExact hsafeTyExact hshapeExact hwellTyExact
    hnotWriteApprox hcohOutExact hrhsTargetsOutExact
  have happroxLval :
      LValTyping approxIn (.var x) (.ty approxSelectedSlotTy)
        approxSlot.lifetime := by
    rw [← happroxSlotTy]
    exact LValTyping.var happroxSlot
  have houtMap :
      EnvSameShapeStrengthening
        (exactIn.update x { exactSlot with ty := .ty exactRhsTy })
        approxOut :=
    EnvWrite.selected_lval_exact_update_to_approx_result_map_ty_strengthening
      hmapExactApprox hexactSlot happroxSlot hstrength hφApprox
      hwellApprox hsafeApprox hheap happroxLval
      (by simp [ProgramStore.loc, VariableProjection])
      happroxSlotTy hwriteApprox
  have hborrowOut :
      BorrowSafeEnv
        (exactIn.update x { exactSlot with ty := .ty exactRhsTy }) := by
    simpa using
      (borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv
        (x := x) (ty := exactRhsTy) (lifetime := exactSlot.lifetime)
        hborrowExact hsafeTyExact)
  have hwriteExact :
      EnvWrite 0 exactIn (.var x) exactRhsTy
        (exactIn.update x { exactSlot with ty := .ty exactRhsTy }) :=
    EnvWrite.intro hexactSlot UpdateAtPath.strong
  have hbelowExactRhs :
      EnvWriteRhsBorrowTargetsBelow φ approxOut exactRhsTy :=
    EnvWriteRhsBorrowTargetsBelow.of_rhs_strengthening hstrength hbelowApprox
  exact
    ExactAssignTransport.of_core_and_approx_guards_wellFormedParts
      hwellExact hmapExactApprox hφApprox hbelowExactRhs hnotWriteApprox
      (LValTyping.var hexactSlot) hshapeExact hwellTyExact hwriteExact
      hcohOutExact hrhsTargetsOutExact hborrowOut houtMap

/--
Selected variable-location dereference transport, with the remaining exact
static write obligations left explicit.

This packages the runtime-selected-variable map for `*source := value`: once an
exact selected update can also be justified as the exact static assignment
output, all rank and write-prohibition guards still come from the approximate
typing result.  For borrowed-target dereferences, the explicit `EnvWrite`
premise below is the important proof frontier: fan-out writes normally produce a
weak branch result, so this theorem records exactly what would be needed to use
the selected strong update as the strict preservation output.
-/
theorem ExactAssignTransport.deref_lval_of_approx_selected
    {store : ProgramStore} {lifetime targetLifetime rhsWellLifetime : Lifetime}
    {source : LVal} {oldTy : PartialTy}
    {rhsTy approxLvTy approxSelectedSlotTy : Ty} {selectedName : Name}
    {exactIn approxIn approxOut : Env}
    {exactSlot approxSlot : EnvSlot} {φ : Name → Nat} :
    EnvSameShapeStrengthening exactIn approxIn →
    exactIn.slotAt selectedName = some exactSlot →
    approxIn.slotAt selectedName = some approxSlot →
    approxSlot.ty = .ty approxSelectedSlotTy →
    LinearizedBy φ approxIn →
    WellFormedEnv approxIn lifetime →
    store ∼ₛ approxIn →
    StoreOwnerTargetsHeap store →
    LValTyping approxIn (.deref source) (.ty approxLvTy) targetLifetime →
    store.loc (.deref source) = some (VariableProjection selectedName) →
    EnvWrite 0 approxIn (.deref source) rhsTy approxOut →
    EnvWriteRhsBorrowTargetsBelow φ approxOut rhsTy →
    ¬ WriteProhibited approxOut (.deref source) →
    WellFormedEnv exactIn lifetime →
    BorrowSafeEnv exactIn →
    TyBorrowSafeAgainstEnv approxIn rhsTy →
    LValTyping exactIn (.deref source) oldTy targetLifetime →
    ShapeCompatible exactIn oldTy (.ty rhsTy) →
    WellFormedTy exactIn rhsTy rhsWellLifetime →
    EnvWrite 0 exactIn (.deref source) rhsTy
      (exactIn.update selectedName { exactSlot with ty := .ty rhsTy }) →
    Coherent
      (exactIn.update selectedName { exactSlot with ty := .ty rhsTy }) →
    EnvWriteRhsTargetsWellFormed
      (exactIn.update selectedName { exactSlot with ty := .ty rhsTy })
      rhsTy →
    ExactAssignTransport lifetime (.deref source) rhsTy exactIn
      (exactIn.update selectedName { exactSlot with ty := .ty rhsTy })
      approxOut oldTy targetLifetime rhsWellLifetime := by
  intro hmapExactApprox hexactSlot happroxSlot happroxSlotTy hφApprox
    hwellApprox hsafeApprox hheap hlvApprox hloc hwriteApprox hbelowApprox
    hnotWriteApprox hwellExact hborrowExact hsafeTyApprox hlvExact
    hshapeExact hwellTyExact hwriteExact hcohOutExact hrhsTargetsOutExact
  have houtMap :
      EnvSameShapeStrengthening
        (exactIn.update selectedName { exactSlot with ty := .ty rhsTy })
        approxOut :=
    EnvWrite.selected_lval_exact_update_to_approx_result_map
      hmapExactApprox hexactSlot happroxSlot hφApprox hwellApprox
      hsafeApprox hheap hlvApprox hloc happroxSlotTy hwriteApprox
  have hborrowOut :
      BorrowSafeEnv
        (exactIn.update selectedName { exactSlot with ty := .ty rhsTy }) :=
    BorrowSafeEnv.update_of_approx_tyBorrowSafe hmapExactApprox hborrowExact
      hsafeTyApprox hexactSlot
  exact
    ExactAssignTransport.of_core_and_approx_guards_wellFormedParts
      hwellExact hmapExactApprox hφApprox hbelowApprox hnotWriteApprox
      hlvExact hshapeExact hwellTyExact hwriteExact hcohOutExact
      hrhsTargetsOutExact hborrowOut houtMap

/--
Typed selected variable-location dereference transport.

This differs from `deref_lval_of_approx_selected` only in the RHS type:
the exact selected update writes `exactRhsTy`, while the approximate fan-out
write uses `approxRhsTy`.
-/
theorem ExactAssignTransport.deref_lval_of_approx_selected_typed
    {store : ProgramStore} {lifetime targetLifetime rhsWellLifetime : Lifetime}
    {source : LVal} {oldTy : PartialTy}
    {exactRhsTy approxRhsTy approxLvTy approxSelectedSlotTy : Ty}
    {selectedName : Name}
    {exactIn approxIn approxOut : Env}
    {exactSlot approxSlot : EnvSlot} {φ : Name → Nat} :
    EnvSameShapeStrengthening exactIn approxIn →
    exactIn.slotAt selectedName = some exactSlot →
    approxIn.slotAt selectedName = some approxSlot →
    approxSlot.ty = .ty approxSelectedSlotTy →
    PartialTyStrengthens (.ty exactRhsTy) (.ty approxRhsTy) →
    LinearizedBy φ approxIn →
    WellFormedEnv approxIn lifetime →
    store ∼ₛ approxIn →
    StoreOwnerTargetsHeap store →
    LValTyping approxIn (.deref source) (.ty approxLvTy) targetLifetime →
    store.loc (.deref source) = some (VariableProjection selectedName) →
    EnvWrite 0 approxIn (.deref source) approxRhsTy approxOut →
    EnvWriteRhsBorrowTargetsBelow φ approxOut approxRhsTy →
    ¬ WriteProhibited approxOut (.deref source) →
    WellFormedEnv exactIn lifetime →
    BorrowSafeEnv exactIn →
    TyBorrowSafeAgainstEnv exactIn exactRhsTy →
    LValTyping exactIn (.deref source) oldTy targetLifetime →
    ShapeCompatible exactIn oldTy (.ty exactRhsTy) →
    WellFormedTy exactIn exactRhsTy rhsWellLifetime →
    EnvWrite 0 exactIn (.deref source) exactRhsTy
      (exactIn.update selectedName
        { exactSlot with ty := .ty exactRhsTy }) →
    Coherent
      (exactIn.update selectedName
        { exactSlot with ty := .ty exactRhsTy }) →
    EnvWriteRhsTargetsWellFormed
      (exactIn.update selectedName
        { exactSlot with ty := .ty exactRhsTy })
      exactRhsTy →
    ExactAssignTransport lifetime (.deref source) exactRhsTy exactIn
      (exactIn.update selectedName
        { exactSlot with ty := .ty exactRhsTy })
      approxOut oldTy targetLifetime rhsWellLifetime := by
  intro hmapExactApprox hexactSlot happroxSlot happroxSlotTy hstrength
    hφApprox hwellApprox hsafeApprox hheap hlvApprox hloc hwriteApprox
    hbelowApprox hnotWriteApprox hwellExact hborrowExact hsafeTyExact
    hlvExact hshapeExact hwellTyExact hwriteExact hcohOutExact
    hrhsTargetsOutExact
  have houtMap :
      EnvSameShapeStrengthening
        (exactIn.update selectedName
          { exactSlot with ty := .ty exactRhsTy })
        approxOut :=
    EnvWrite.selected_lval_exact_update_to_approx_result_map_ty_strengthening
      hmapExactApprox hexactSlot happroxSlot hstrength hφApprox
      hwellApprox hsafeApprox hheap hlvApprox hloc happroxSlotTy
      hwriteApprox
  have hborrowOut :
      BorrowSafeEnv
        (exactIn.update selectedName
          { exactSlot with ty := .ty exactRhsTy }) := by
    simpa using
      (borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv
        (x := selectedName) (ty := exactRhsTy)
        (lifetime := exactSlot.lifetime) hborrowExact hsafeTyExact)
  have hbelowExactRhs :
      EnvWriteRhsBorrowTargetsBelow φ approxOut exactRhsTy :=
    EnvWriteRhsBorrowTargetsBelow.of_rhs_strengthening hstrength hbelowApprox
  exact
    ExactAssignTransport.of_core_and_approx_guards_wellFormedParts
      hwellExact hmapExactApprox hφApprox hbelowExactRhs hnotWriteApprox
      hlvExact hshapeExact hwellTyExact hwriteExact hcohOutExact
      hrhsTargetsOutExact hborrowOut houtMap

/--
Selected heap-location dereference transport, with the exact static write left
explicit.

The selected owner-spine map proves the exact strong leaf update strengthens to
the approximate fan-out result.  Approximate RHS borrow-safety supplies
`BorrowSafeEnv` for the nested exact output, so the remaining local obligations
are the exact lvalue/write/well-formedness facts.
-/
theorem ExactAssignTransport.deref_spine_of_approx_selected
    {store : ProgramStore} {lifetime targetLifetime rhsWellLifetime : Lifetime}
    {source : LVal} {oldTy : PartialTy} {rhsTy approxLvTy : Ty}
    {address : Nat} {xRoot : Name}
    {exactIn approxIn approxOut : Env}
    {exactRootSlot approxRootSlot : EnvSlot}
    {rootSlot leafSlot : StoreSlot} {spinePath : List Unit}
    {leafTy : Ty} {φ : Name → Nat} :
    EnvSameShapeStrengthening exactIn approxIn →
    exactIn.slotAt xRoot = some exactRootSlot →
    approxIn.slotAt xRoot = some approxRootSlot →
    LinearizedBy φ approxIn →
    WellFormedEnv approxIn lifetime →
    store ∼ₛ approxIn →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    StoreOwnerSpine store (VariableProjection xRoot) rootSlot
      approxRootSlot.ty spinePath (.heap address) leafSlot (.ty leafTy) →
    spinePath ≠ [] →
    LValTyping approxIn (.deref source) (.ty approxLvTy) targetLifetime →
    store.loc (.deref source) = some (.heap address) →
    EnvWrite 0 approxIn (.deref source) rhsTy approxOut →
    EnvWriteRhsBorrowTargetsBelow φ approxOut rhsTy →
    ¬ WriteProhibited approxOut (.deref source) →
    WellFormedEnv exactIn lifetime →
    BorrowSafeEnv exactIn →
    TyBorrowSafeAgainstEnv approxIn rhsTy →
    LValTyping exactIn (.deref source) oldTy targetLifetime →
    ShapeCompatible exactIn oldTy (.ty rhsTy) →
    WellFormedTy exactIn rhsTy rhsWellLifetime →
    EnvWrite 0 exactIn (.deref source) rhsTy
      (exactIn.update xRoot
        { exactRootSlot with
            ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
              rhsTy }) →
    Coherent
      (exactIn.update xRoot
        { exactRootSlot with
            ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
              rhsTy })
       →
    EnvWriteRhsTargetsWellFormed
      (exactIn.update xRoot
        { exactRootSlot with
            ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
              rhsTy })
      rhsTy →
    ExactAssignTransport lifetime (.deref source) rhsTy exactIn
      (exactIn.update xRoot
        { exactRootSlot with
            ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
              rhsTy })
      approxOut oldTy targetLifetime rhsWellLifetime := by
  intro hmapExactApprox hexactRoot happroxRoot hφApprox hwellApprox
    hsafeApprox hvalidStore hheap hspine hspineNonempty hlvApprox hloc
    hwriteApprox hbelowApprox hnotWriteApprox hwellExact hborrowExact
    hsafeTyApprox hlvExact hshapeExact hwellTyExact hwriteExact hcohOutExact
    hrhsTargetsOutExact
  have houtMap :
      EnvSameShapeStrengthening
        (exactIn.update xRoot
          { exactRootSlot with
              ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
                rhsTy })
        approxOut :=
    EnvWrite.selected_spine_exact_update_to_approx_result_map
      hmapExactApprox hexactRoot happroxRoot hφApprox hwellApprox
      hsafeApprox hvalidStore hheap hspine hspineNonempty hlvApprox hloc
      hwriteApprox
  have hborrowOutExact :
      BorrowSafeEnv
        (exactIn.update xRoot
          { exactRootSlot with
              ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
                rhsTy }) :=
    BorrowSafeEnv.update_strongLeafUpdate_of_approx_tyBorrowSafe
      hmapExactApprox hborrowExact hsafeTyApprox hexactRoot
  exact
    ExactAssignTransport.of_core_and_approx_guards_wellFormedParts
      hwellExact hmapExactApprox hφApprox hbelowApprox hnotWriteApprox
      hlvExact hshapeExact hwellTyExact hwriteExact hcohOutExact
      hrhsTargetsOutExact hborrowOutExact houtMap

/--
Typed selected heap-location dereference transport.

The selected exact owner spine is updated with `exactRhsTy`; the approximate
write may still be the joined/fan-out result using `approxRhsTy`.
-/
theorem ExactAssignTransport.deref_spine_of_approx_selected_typed
    {store : ProgramStore} {lifetime targetLifetime rhsWellLifetime : Lifetime}
    {source : LVal} {oldTy : PartialTy}
    {exactRhsTy approxRhsTy approxLvTy : Ty}
    {address : Nat} {xRoot : Name}
    {exactIn approxIn approxOut : Env}
    {exactRootSlot approxRootSlot : EnvSlot}
    {rootSlot leafSlot : StoreSlot} {spinePath : List Unit}
    {leafTy : Ty} {φ : Name → Nat} :
    EnvSameShapeStrengthening exactIn approxIn →
    exactIn.slotAt xRoot = some exactRootSlot →
    approxIn.slotAt xRoot = some approxRootSlot →
    PartialTyStrengthens (.ty exactRhsTy) (.ty approxRhsTy) →
    LinearizedBy φ approxIn →
    WellFormedEnv approxIn lifetime →
    store ∼ₛ approxIn →
    ValidStore store →
    StoreOwnerTargetsHeap store →
    StoreOwnerSpine store (VariableProjection xRoot) rootSlot
      approxRootSlot.ty spinePath (.heap address) leafSlot (.ty leafTy) →
    spinePath ≠ [] →
    LValTyping approxIn (.deref source) (.ty approxLvTy) targetLifetime →
    store.loc (.deref source) = some (.heap address) →
    EnvWrite 0 approxIn (.deref source) approxRhsTy approxOut →
    EnvWriteRhsBorrowTargetsBelow φ approxOut approxRhsTy →
    ¬ WriteProhibited approxOut (.deref source) →
    WellFormedEnv exactIn lifetime →
    BorrowSafeEnv exactIn →
    TyBorrowSafeAgainstEnv exactIn exactRhsTy →
    LValTyping exactIn (.deref source) oldTy targetLifetime →
    ShapeCompatible exactIn oldTy (.ty exactRhsTy) →
    WellFormedTy exactIn exactRhsTy rhsWellLifetime →
    EnvWrite 0 exactIn (.deref source) exactRhsTy
      (exactIn.update xRoot
        { exactRootSlot with
            ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
              exactRhsTy }) →
    Coherent
      (exactIn.update xRoot
        { exactRootSlot with
            ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
              exactRhsTy })
       →
    EnvWriteRhsTargetsWellFormed
      (exactIn.update xRoot
        { exactRootSlot with
            ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
              exactRhsTy })
      exactRhsTy →
    ExactAssignTransport lifetime (.deref source) exactRhsTy exactIn
      (exactIn.update xRoot
        { exactRootSlot with
            ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
              exactRhsTy })
      approxOut oldTy targetLifetime rhsWellLifetime := by
  intro hmapExactApprox hexactRoot happroxRoot hstrength hφApprox
    hwellApprox hsafeApprox hvalidStore hheap hspine hspineNonempty
    hlvApprox hloc hwriteApprox hbelowApprox hnotWriteApprox hwellExact
    hborrowExact hsafeTyExact hlvExact hshapeExact hwellTyExact hwriteExact
    hcohOutExact hrhsTargetsOutExact
  have houtMap :
      EnvSameShapeStrengthening
        (exactIn.update xRoot
          { exactRootSlot with
              ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
                exactRhsTy })
        approxOut :=
    EnvWrite.selected_spine_exact_update_to_approx_result_map_ty_strengthening
      hmapExactApprox hexactRoot happroxRoot hstrength hφApprox hwellApprox
      hsafeApprox hvalidStore hheap hspine hspineNonempty hlvApprox hloc
      hwriteApprox
  have hborrowOutExact :
      BorrowSafeEnv
        (exactIn.update xRoot
          { exactRootSlot with
              ty := PartialTy.strongLeafUpdate exactRootSlot.ty spinePath
                exactRhsTy }) :=
    BorrowSafeEnv.update_strongLeafUpdate_of_approx_tyBorrowSafe
      (EnvSameShapeStrengthening.refl exactIn) hborrowExact hsafeTyExact
      hexactRoot
  have hbelowExactRhs :
      EnvWriteRhsBorrowTargetsBelow φ approxOut exactRhsTy :=
    EnvWriteRhsBorrowTargetsBelow.of_rhs_strengthening hstrength hbelowApprox
  exact
    ExactAssignTransport.of_core_and_approx_guards_wellFormedParts
      hwellExact hmapExactApprox hφApprox hbelowExactRhs hnotWriteApprox
      hlvExact hshapeExact hwellTyExact hwriteExact hcohOutExact
      hrhsTargetsOutExact hborrowOutExact houtMap

/-! ## Move frontier -/

/--
Move typing/runtime facts re-established for the exact runtime path.

`EnvMove` strikes exactly one selected root/spine.  Under a relaxed `if` join,
the approximate move output may be a weakened/fan-out result while the runtime
path only updates the selected exact environment.  This package records the
exact move output plus the map back to the approximate continuation
environment.
-/
structure ExactMoveTransport (lifetime : Lifetime) (lv : LVal)
    (approxTy exactTy : Ty) (exactIn exactOut approxOut : Env)
    (valueLifetime : Lifetime) : Prop where
  lval : LValTyping exactIn lv (.ty exactTy) valueLifetime
  resultStrength : PartialTyStrengthens (.ty exactTy) (.ty approxTy)
  notWrite : ¬ WriteProhibited exactIn lv
  move : EnvMove exactIn lv exactOut
  wellOut : WellFormedEnv exactOut lifetime
  borrowOut : BorrowSafeEnv exactOut
  outMap : EnvSameShapeStrengthening exactOut approxOut

/--
Build exact move transport from exact-side typing facts and the output map.
Borrow safety of the exact output is local to `EnvMove`; it does not require any
borrow-safety fact for the approximate continuation environment.
-/
theorem ExactMoveTransport.of_exact_parts
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    {exactTy : Ty} {exactIn exactOut approxOut : Env} :
    WellFormedEnv exactIn lifetime →
    BorrowSafeEnv exactIn →
    LValTyping exactIn lv (.ty exactTy) valueLifetime →
    PartialTyStrengthens (.ty exactTy) (.ty ty) →
    ¬ WriteProhibited exactIn lv →
    EnvMove exactIn lv exactOut →
    EnvSameShapeStrengthening exactOut approxOut →
    ExactMoveTransport lifetime lv ty exactTy exactIn exactOut approxOut
      valueLifetime := by
  intro hwellExact hborrowExact hlv hresultStrength hnotWrite hmove houtMap
  exact
    { lval := hlv
      resultStrength := hresultStrength
      notWrite := hnotWrite
      move := hmove
      wellOut := (move_preserves_wellFormed hwellExact hlv hnotWrite hmove).1
      borrowOut := borrowSafeEnv_move hborrowExact hmove
      outMap := houtMap }

/--
Variable moves are already path-selected.

If the approximate environment moves a variable with a full type, any exact
environment that same-shape strengthens to it has a corresponding full type for
that variable.  Striking the exact variable to `undef` gives an exact move
output that strengthens to the approximate move output.
-/
theorem ExactMoveTransport.var_of_approx_selected
    {lifetime : Lifetime} {x : Name} {approxTy : Ty}
    {exactIn approxIn approxOut : Env} {approxSlot : EnvSlot} :
    EnvSameShapeStrengthening exactIn approxIn →
    approxIn.slotAt x = some approxSlot →
    approxSlot.ty = .ty approxTy →
    WellFormedEnv exactIn lifetime →
    BorrowSafeEnv exactIn →
    ¬ WriteProhibited approxIn (.var x) →
    EnvMove approxIn (.var x) approxOut →
    ∃ exactOut exactTy valueLifetime,
      ExactMoveTransport lifetime (.var x) approxTy exactTy exactIn exactOut
        approxOut valueLifetime := by
  intro hmapExactApprox happroxSlot happroxSlotTy hwellExact hborrowExact
    hnotWriteApprox hmoveApprox
  rcases hmapExactApprox.1 x approxSlot happroxSlot with
    ⟨exactSlot, hexactSlot, _hlifetime, hstrengthSlot, _hshape⟩
  have hstrengthTy : PartialTyStrengthens exactSlot.ty (.ty approxTy) := by
    simpa [happroxSlotTy] using hstrengthSlot
  rcases PartialTyStrengthens.to_ty_right hstrengthTy with
    ⟨exactTy, hexactSlotTy⟩
  have hresultStrength :
      PartialTyStrengthens (.ty exactTy) (.ty approxTy) := by
    simpa [hexactSlotTy] using hstrengthTy
  have hlvExact :
      LValTyping exactIn (.var x) (.ty exactTy) exactSlot.lifetime := by
    simpa [hexactSlotTy] using (LValTyping.var hexactSlot)
  have hnotWriteExact : ¬ WriteProhibited exactIn (.var x) := by
    intro hwriteExact
    exact hnotWriteApprox
      (WriteProhibited.of_sameShapeStrengthening hmapExactApprox hwriteExact)
  have hmoveExact :
      EnvMove exactIn (.var x)
        (exactIn.update x { exactSlot with ty := .undef exactTy }) := by
    refine ⟨exactSlot, .undef exactTy, hexactSlot, ?_, rfl⟩
    simp [LVal.path, Strike, hexactSlotTy]
  rcases hmoveApprox with
    ⟨approxMoveSlot, approxStruck, happroxMoveSlot, hstrikeApprox,
      happroxOut⟩
  have happroxMoveSlotEq : approxMoveSlot = approxSlot :=
    Option.some.inj (happroxMoveSlot.symm.trans happroxSlot)
  subst approxMoveSlot
  have happroxStruckEq : approxStruck = .undef approxTy := by
    cases approxStruck with
    | ty targetTy =>
        simp [LVal.path, Strike, happroxSlotTy] at hstrikeApprox
    | «box» inner =>
        simp [LVal.path, Strike, happroxSlotTy] at hstrikeApprox
    | undef targetTy =>
        simp [LVal.path, Strike, happroxSlotTy] at hstrikeApprox
        cases hstrikeApprox
        rfl
  rw [happroxStruckEq] at happroxOut
  simp [LVal.base] at happroxOut
  subst approxOut
  have houtMap :
      EnvSameShapeStrengthening
        (exactIn.update x { exactSlot with ty := .undef exactTy })
        (approxIn.update x { approxSlot with ty := .undef approxTy }) :=
    EnvSameShapeStrengthening.update_both_undef_ty hmapExactApprox
      hexactSlot happroxSlot hresultStrength
  exact ⟨_, exactTy, exactSlot.lifetime,
    ExactMoveTransport.of_exact_parts hwellExact hborrowExact hlvExact
      hresultStrength hnotWriteExact hmoveExact houtMap⟩

/--
If a move redex can be transported from the approximate environment to the
exact runtime environment, path-sensitive preservation follows from the
existing strict move-preservation lemmas.

The hard part is `htransport`: reconstructing the exact `EnvMove` result and
showing it strengthens to the approximate output.
-/
theorem pathSensitive_move_case_of_exactTransport
    {store finalStore : ProgramStore} {lifetime : Lifetime}
    {typing : StoreTyping} {lv : LVal} {ty : Ty} {finalValue : Value}
    {approxIn approxOut : Env} :
    RuntimeExactEnvWitness store lifetime approxIn →
    ValidRuntimeState store (.move lv) →
    WellFormedEnv approxOut lifetime →
    MultiStep store lifetime (.move lv) finalStore (.val finalValue) →
    (∀ exactIn,
      WellFormedEnv exactIn lifetime →
      BorrowSafeEnv exactIn →
      store ∼ₛ exactIn →
      EnvSameShapeStrengthening exactIn approxIn →
      ∃ exactOut exactTy valueLifetime,
        ExactMoveTransport lifetime lv ty exactTy exactIn exactOut approxOut
          valueLifetime) →
    PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxOut
      ty := by
  intro hwitness hvalidRuntime hwellApproxOut hmulti htransport
  rcases hwitness with
    ⟨exactIn, hwellExact, hborrowExact, hsafeExact, hmapExactApprox⟩
  rcases htransport exactIn hwellExact hborrowExact hsafeExact
      hmapExactApprox with
    ⟨exactOut, exactTy, valueLifetime, hmoveExact⟩
  have htermTyping :
      TermTyping exactIn typing lifetime (.move lv) exactTy exactOut :=
    TermTyping.move hmoveExact.lval hmoveExact.notWrite hmoveExact.move
  have hterminalExact :
      TerminalStateSafe finalStore finalValue exactOut exactTy := by
    cases lv with
    | var x =>
        rcases LValTyping.var_inv hmoveExact.lval with
          ⟨slot, hslot, htyEq, hlifetimeEq⟩
        cases slot with
        | mk slotTy slotLifetime =>
            cases htyEq
            cases hlifetimeEq
            exact preservation_move_var_multistep_runtime_of_wellFormed
              hwellExact hsafeExact hvalidRuntime hslot hmoveExact.move
              htermTyping hmulti
    | deref source =>
        cases hmoveExact.lval with
        | «box» hsourceBox =>
            exact preservation_move_deref_box_multistep_runtime_of_wellFormed
              hwellExact hsafeExact hvalidRuntime hsourceBox
              hmoveExact.notWrite hmoveExact.move htermTyping hmulti
        | borrow hsourceBorrow _htargets =>
            exact False.elim (by
              rcases hmoveExact.move with
                ⟨moveSlot, struck, hslot, hstrike, _hout⟩
              have hsourceSlot :
              exactIn.slotAt (LVal.base source) = some moveSlot := by
                simpa [LVal.base] using hslot
              have hleaf :
                  WriteLeafTy exactIn (LVal.path source) moveSlot.ty
                    Ty.unit := by
                simpa using
                  (writeLeafTy_of_lvalTyping hsourceBorrow hsourceSlot []
                    Ty.unit WriteLeafTy.leaf)
              exact WriteLeafTy.not_strike_deref hleaf
                (by simpa [LVal.path_deref_cons] using hstrike))
  have hsafeExactPath :
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue exactOut
        exactTy :=
    ⟨hterminalExact,
      ⟨exactOut, hmoveExact.wellOut, hmoveExact.borrowOut,
        hterminalExact.2.1, EnvSameShapeStrengthening.refl exactOut⟩⟩
  exact PathSensitiveTerminalStateSafe.strengthen hwellApproxOut
    hmoveExact.outMap hmoveExact.resultStrength hsafeExactPath

/--
The full relaxed `T-Move` case reduces to exact move transport.

The approximate environment's well-formedness is preserved by the existing
`move_preserves_wellFormed` theorem.  Runtime safety for continuation code is
path-sensitive and comes from `htransport`, not from a borrow-safe approximate
post-environment.
-/
theorem relaxed_preservation_move_case_of_exactTransport
    {store finalStore : ProgramStore} {approxIn approxOut : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {lv : LVal} {ty : Ty} {finalValue : Value} :
    SourceTerm (.move lv) →
    ValidRuntimeState store (.move lv) →
    ValidStoreTyping store (.move lv) typing →
    WellFormedEnv approxIn lifetime →
    RuntimeExactEnvWitness store lifetime approxIn →
    LValTyping approxIn lv (.ty ty) valueLifetime →
    ¬ WriteProhibited approxIn lv →
    EnvMove approxIn lv approxOut →
    (∀ exactIn,
      WellFormedEnv exactIn lifetime →
      BorrowSafeEnv exactIn →
      store ∼ₛ exactIn →
      EnvSameShapeStrengthening exactIn approxIn →
      ∃ exactOut exactTy valueLifetime,
        ExactMoveTransport lifetime lv ty exactTy exactIn exactOut approxOut
          valueLifetime) →
    MultiStep store lifetime (.move lv) finalStore (.val finalValue) →
    WellFormedEnv approxOut lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxOut
      ty := by
  intro _hsource hvalidRuntime _hvalidStoreTyping hwellApproxIn hwitness
    hlv hnotWrite hmove htransport hmulti
  have hwellOut : WellFormedEnv approxOut lifetime :=
    (move_preserves_wellFormed hwellApproxIn hlv hnotWrite hmove).1
  have hterminal :
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxOut
        ty :=
    pathSensitive_move_case_of_exactTransport
      (typing := typing) hwitness hvalidRuntime hwellOut hmulti htransport
  exact ⟨hwellOut, hterminal⟩

/--
The variable `T-Move` redex needs no extra frontier assumption.

`LValTyping.var_inv` exposes the approximate slot, and
`ExactMoveTransport.var_of_approx_selected` reconstructs the selected exact
move output for every runtime exact witness.
-/
theorem relaxed_preservation_move_var_case
    {store finalStore : ProgramStore} {approxIn approxOut : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {x : Name} {ty : Ty} {finalValue : Value} :
    SourceTerm (.move (.var x)) →
    ValidRuntimeState store (.move (.var x)) →
    ValidStoreTyping store (.move (.var x)) typing →
    WellFormedEnv approxIn lifetime →
    RuntimeExactEnvWitness store lifetime approxIn →
    LValTyping approxIn (.var x) (.ty ty) valueLifetime →
    ¬ WriteProhibited approxIn (.var x) →
    EnvMove approxIn (.var x) approxOut →
    MultiStep store lifetime (.move (.var x)) finalStore (.val finalValue) →
    WellFormedEnv approxOut lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxOut
        ty := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness
    hlv hnotWrite hmove hmulti
  refine relaxed_preservation_move_case_of_exactTransport
    (typing := typing) hsource hvalidRuntime hvalidStoreTyping hwellApproxIn
    hwitness hlv hnotWrite hmove ?_ hmulti
  intro exactIn hwellExact hborrowExact _hsafeExact hmapExactApprox
  rcases LValTyping.var_inv hlv with
    ⟨approxSlot, happroxSlot, happroxSlotTy, _happroxLifetime⟩
  exact ExactMoveTransport.var_of_approx_selected hmapExactApprox
    happroxSlot happroxSlotTy hwellExact hborrowExact hnotWrite hmove

/-! ## Box frontier -/

/--
Path-sensitive preservation for the `box` redex.

The ordinary runtime proof is the existing strict allocation lemma, run against
the approximate environment.  The exact witness is threaded separately by
`RuntimeExactEnvWitness.box_redex`; no borrow-safety fact about the approximate
environment is needed.
-/
theorem pathSensitive_box_redex_case
    {store store' : ProgramStore} {approxEnv : Env}
    {lifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    RuntimeExactEnvWitness store lifetime approxEnv →
    ValidRuntimeState store (.box (.val value)) →
    ValidValue store value ty →
    Step store lifetime (.box (.val value)) store' (.val finalValue) →
    PathSensitiveTerminalStateSafe store' lifetime finalValue approxEnv
      (.box ty) := by
  intro hwitness hvalidRuntime hvalidValue hstep
  cases hstep with
  | «box» hfresh hbox =>
      have hterminal :=
        preservation_box_redex_runtime_of_validValue
          (RuntimeExactEnvWitness.safe hwitness) hvalidRuntime hvalidValue
          (Step.box (lifetime := lifetime) hfresh hbox)
      exact ⟨hterminal,
        RuntimeExactEnvWitness.box_redex hwitness
          (Step.box (lifetime := lifetime) hfresh hbox)⟩

/--
Typed path-sensitive preservation for the `box` redex.

The approximate terminal result is the ordinary box result, while the exact
runtime witness boxes the selected exact operand type.
-/
theorem pathSensitive_box_redex_typed_case
    {store store' : ProgramStore} {approxEnv : Env}
    {lifetime : Lifetime} {value finalValue : Value} {ty : Ty} :
    PathSensitiveTypedTerminalStateSafe store lifetime value approxEnv ty →
    ValidRuntimeState store (.box (.val value)) →
    Step store lifetime (.box (.val value)) store' (.val finalValue) →
    PathSensitiveTypedTerminalStateSafe store' lifetime finalValue approxEnv
      (.box ty) := by
  intro hsafeTyped hvalidRuntime hstep
  cases hstep with
  | «box» hfresh hbox =>
      have hpath :=
        pathSensitive_box_redex_case
          (RuntimeExactTypedValueWitness.to_runtime hsafeTyped.2)
          hvalidRuntime hsafeTyped.1.2.2
          (Step.box (lifetime := lifetime) hfresh hbox)
      rcases hsafeTyped.2 with
        ⟨exactEnv, exactTy, hwellExact, hborrowExact, hsafeExact,
          hmapExactApprox, hstrength, hvalidExact, hwellTyExact,
          hsafeTyExact⟩
      have hterminalExact :=
        preservation_box_redex_runtime_of_validValue hsafeExact hvalidRuntime
          hvalidExact (Step.box (lifetime := lifetime) hfresh hbox)
      exact ⟨hpath.1,
        ⟨exactEnv, .box exactTy, hwellExact, hborrowExact,
          hterminalExact.2.1, hmapExactApprox,
          PartialTyStrengthens.tyBox hstrength, hterminalExact.2.2,
          WellFormedTy.box hwellTyExact,
          TyBorrowSafeAgainstEnv.box hsafeTyExact⟩⟩

/--
The relaxed `T-Box` preservation case reduces to the operand IH.

After the operand reaches a value, the box redex allocates a fresh heap cell
without changing the environment.  The operand IH already provides the exact
runtime witness for the output environment, so allocation can preserve that
witness directly.
-/
theorem relaxed_preservation_box_case
    {store finalStore : ProgramStore} {approxIn approxOut : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} {finalValue : Value} :
    SourceTerm (.box term) →
    ValidRuntimeState store (.box term) →
    ValidStoreTyping store (.box term) typing →
    WellFormedEnv approxIn lifetime →
    RuntimeExactEnvWitness store lifetime approxIn →
    RelaxedTermTyping approxIn typing lifetime term ty approxOut →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT term →
      ValidStoreTyping storeT term typing →
      WellFormedEnv approxIn lifetime →
      RuntimeExactEnvWitness storeT lifetime approxIn →
      MultiStep storeT lifetime term finalStoreT (.val finalValueT) →
      WellFormedEnv approxOut lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreT lifetime finalValueT
          approxOut ty) →
    MultiStep store lifetime (.box term) finalStore (.val finalValue) →
    WellFormedEnv approxOut lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxOut
        (.box ty) := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness hinner
    ihInner hmulti
  rcases multistep_box_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hboxStep⟩
  have htermTyping :
      RelaxedTermTyping approxIn typing lifetime (.box term) (.box ty)
        approxOut :=
    RelaxedTermTyping.box hinner
  have hwellOut : WellFormedEnv approxOut lifetime :=
    (relaxed_typingPreservesWellFormed_of_sourceTerm hsource
      (ValidRuntimeState.validState hvalidRuntime) hwellApproxIn
      (RuntimeExactEnvWitness.safe hwitness) htermTyping).1
  rcases ihInner
      (validRuntimeState_box_inner hvalidRuntime)
      (validStoreTyping_box_inner hvalidStoreTyping)
      hwellApproxIn hwitness hinnerMulti with
    ⟨_hwellOperandOut, hterminalOperand⟩
  have hvalidBoxValue : ValidRuntimeState midStore (.box (.val value)) :=
    validRuntimeState_box_value_of_value hterminalOperand.1.1
  have hterminalBox :
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxOut
        (.box ty) :=
    pathSensitive_box_redex_case hterminalOperand.2 hvalidBoxValue
      hterminalOperand.1.2.2 hboxStep
  exact ⟨hwellOut, hterminalBox⟩

/--
Typed relaxed `T-Box` preservation case.

The operand IH supplies the exact runtime type of the produced value; the final
redex boxes that exact type and weakens it back to the approximate boxed type.
-/
theorem relaxed_preservation_box_typed_case
    {store finalStore : ProgramStore} {approxIn approxOut : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} {finalValue : Value} :
    SourceTerm (.box term) →
    ValidRuntimeState store (.box term) →
    ValidStoreTyping store (.box term) typing →
    WellFormedEnv approxIn lifetime →
    RuntimeExactEnvWitness store lifetime approxIn →
    RelaxedTermTyping approxIn typing lifetime term ty approxOut →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT term →
      ValidStoreTyping storeT term typing →
      WellFormedEnv approxIn lifetime →
      RuntimeExactEnvWitness storeT lifetime approxIn →
      MultiStep storeT lifetime term finalStoreT (.val finalValueT) →
      WellFormedEnv approxOut lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreT lifetime finalValueT
          approxOut ty) →
    MultiStep store lifetime (.box term) finalStore (.val finalValue) →
    WellFormedEnv approxOut lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue
        approxOut (.box ty) := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness hinner
    ihInner hmulti
  rcases multistep_box_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hboxStep⟩
  have htermTyping :
      RelaxedTermTyping approxIn typing lifetime (.box term) (.box ty)
        approxOut :=
    RelaxedTermTyping.box hinner
  have hwellOut : WellFormedEnv approxOut lifetime :=
    (relaxed_typingPreservesWellFormed_of_sourceTerm hsource
      (ValidRuntimeState.validState hvalidRuntime) hwellApproxIn
      (RuntimeExactEnvWitness.safe hwitness) htermTyping).1
  rcases ihInner
      (validRuntimeState_box_inner hvalidRuntime)
      (validStoreTyping_box_inner hvalidStoreTyping)
      hwellApproxIn hwitness hinnerMulti with
    ⟨_hwellOperandOut, hterminalOperand⟩
  have hvalidBoxValue : ValidRuntimeState midStore (.box (.val value)) :=
    validRuntimeState_box_value_of_value hterminalOperand.1.1
  have hterminalBox :
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue
        approxOut (.box ty) :=
    pathSensitive_box_redex_typed_case hterminalOperand hvalidBoxValue
      hboxStep
  exact ⟨hwellOut, hterminalBox⟩

/-! ## Redex cases whose store/environment do not change -/

/--
Path-sensitive preservation for `copy` redexes.

The terminal proof runs against the approximate typing environment, using the
ordinary strict copy preservation lemma.  The exact runtime witness persists
because evaluating a copy does not change the store.
-/
theorem pathSensitive_copy_case
    {store finalStore : ProgramStore} {approxEnv : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {lv : LVal} {ty : Ty} {finalValue : Value} :
    WellFormedEnv approxEnv lifetime →
    RuntimeExactEnvWitness store lifetime approxEnv →
    ValidRuntimeState store (.copy lv) →
    LValTyping approxEnv lv (.ty ty) valueLifetime →
    CopyTy ty →
    ¬ ReadProhibited approxEnv lv →
    MultiStep store lifetime (.copy lv) finalStore (.val finalValue) →
    PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxEnv
      ty := by
  intro hwellApprox hwitness hvalidRuntime hlv hcopy hnotRead hmulti
  have htermTyping :
      TermTyping approxEnv typing lifetime (.copy lv) ty approxEnv :=
    TermTyping.copy hlv hcopy hnotRead
  have hterminal :
      TerminalStateSafe finalStore finalValue approxEnv ty :=
    preservation_copy_multistep_runtime hwellApprox
      (RuntimeExactEnvWitness.safe hwitness) hvalidRuntime htermTyping hmulti
  have hstoreEq : finalStore = store :=
    multistep_copy_to_value_store_eq hmulti
  exact ⟨hterminal, RuntimeExactEnvWitness.of_store_eq hstoreEq hwitness⟩

/--
Path-sensitive preservation for mutable borrow redexes.

No borrow-safety fact about `approxEnv` is needed: runtime safety is checked
against `approxEnv`, and the exact borrow-safe witness is unchanged because the
store is unchanged.
-/
theorem pathSensitive_mutBorrow_case
    {store finalStore : ProgramStore} {approxEnv : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {lv : LVal} {ty : Ty} {finalValue : Value} :
    RuntimeExactEnvWitness store lifetime approxEnv →
    ValidRuntimeState store (Term.borrow Bool.true lv) →
    LValTyping approxEnv lv (.ty ty) valueLifetime →
    Mutable approxEnv lv →
    ¬ WriteProhibited approxEnv lv →
    MultiStep store lifetime (Term.borrow Bool.true lv) finalStore
      (.val finalValue) →
    PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxEnv
      (Ty.borrow Bool.true [lv]) := by
  intro hwitness hvalidRuntime hlv hmutable hnotWrite hmulti
  have htermTyping :
      TermTyping approxEnv typing lifetime (Term.borrow Bool.true lv)
        (Ty.borrow Bool.true [lv]) approxEnv :=
    TermTyping.mutBorrow hlv hmutable hnotWrite
  have hterminal :
      TerminalStateSafe finalStore finalValue approxEnv
        (Ty.borrow Bool.true [lv]) :=
    preservation_borrow_multistep_runtime
      (RuntimeExactEnvWitness.safe hwitness) hvalidRuntime htermTyping hmulti
  have hstoreEq : finalStore = store :=
    multistep_borrow_to_value_store_eq hmulti
  exact ⟨hterminal, RuntimeExactEnvWitness.of_store_eq hstoreEq hwitness⟩

/--
Path-sensitive preservation for immutable borrow redexes.  As for mutable
borrows, the store and environment are unchanged.
-/
theorem pathSensitive_immBorrow_case
    {store finalStore : ProgramStore} {approxEnv : Env}
    {typing : StoreTyping} {lifetime valueLifetime : Lifetime}
    {lv : LVal} {ty : Ty} {finalValue : Value} :
    RuntimeExactEnvWitness store lifetime approxEnv →
    ValidRuntimeState store (Term.borrow Bool.false lv) →
    LValTyping approxEnv lv (.ty ty) valueLifetime →
    ¬ ReadProhibited approxEnv lv →
    MultiStep store lifetime (Term.borrow Bool.false lv) finalStore
      (.val finalValue) →
    PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxEnv
      (Ty.borrow Bool.false [lv]) := by
  intro hwitness hvalidRuntime hlv hnotRead hmulti
  have htermTyping :
      TermTyping approxEnv typing lifetime (Term.borrow Bool.false lv)
        (Ty.borrow Bool.false [lv]) approxEnv :=
    TermTyping.immBorrow hlv hnotRead
  have hterminal :
      TerminalStateSafe finalStore finalValue approxEnv
        (Ty.borrow Bool.false [lv]) :=
    preservation_borrow_multistep_runtime
      (RuntimeExactEnvWitness.safe hwitness) hvalidRuntime htermTyping hmulti
  have hstoreEq : finalStore = store :=
    multistep_borrow_to_value_store_eq hmulti
  exact ⟨hterminal, RuntimeExactEnvWitness.of_store_eq hstoreEq hwitness⟩

/-! ## Equality frontier -/

/--
Path-sensitive preservation for the final equality redex.

The comparison redex only returns a Boolean and leaves the store/environment
unchanged, so the exact witness produced by the RHS run is reused directly.
-/
theorem pathSensitive_eq_redex_case
    {store store' : ProgramStore} {approxEnv : Env}
    {lifetime : Lifetime} {leftValue rightValue finalValue : Value}
    {rhsTy : Ty} :
    PathSensitiveTerminalStateSafe store lifetime rightValue approxEnv rhsTy →
    Step store lifetime (.eq (.val leftValue) (.val rightValue)) store'
      (.val finalValue) →
    PathSensitiveTerminalStateSafe store' lifetime finalValue approxEnv
      .bool := by
  intro hsafePath hstep
  cases hstep with
  | eqTrue =>
      exact ⟨
        ⟨validRuntimeState_of_sourceTerm (sourceTerm_bool_value Bool.true)
            hsafePath.1.1,
          hsafePath.1.2.1,
          ValidPartialValue.bool⟩,
        hsafePath.2⟩
  | eqFalse _hne =>
      exact ⟨
        ⟨validRuntimeState_of_sourceTerm (sourceTerm_bool_value Bool.false)
            hsafePath.1.1,
          hsafePath.1.2.1,
          ValidPartialValue.bool⟩,
        hsafePath.2⟩

/--
Typed path-sensitive preservation for the final equality redex.

The exact runtime type after the comparison is just `bool`, regardless of the
RHS exact type used before the redex.
-/
theorem pathSensitive_eq_redex_typed_case
    {store store' : ProgramStore} {approxEnv : Env}
    {lifetime : Lifetime} {leftValue rightValue finalValue : Value}
    {rhsTy : Ty} :
    PathSensitiveTypedTerminalStateSafe store lifetime rightValue approxEnv
      rhsTy →
    Step store lifetime (.eq (.val leftValue) (.val rightValue)) store'
      (.val finalValue) →
    PathSensitiveTypedTerminalStateSafe store' lifetime finalValue approxEnv
      .bool := by
  intro hsafeTyped hstep
  have hpath :
      PathSensitiveTerminalStateSafe store' lifetime finalValue approxEnv
        .bool :=
    pathSensitive_eq_redex_case
      (PathSensitiveTypedTerminalStateSafe.to_pathSensitive hsafeTyped) hstep
  rcases hsafeTyped.2 with
    ⟨exactEnv, _exactTy, hwellExact, hborrowExact, hsafeExact,
      hmapExactApprox, _hstrength, _hvalidExact, _hwellTyExact,
      _hsafeTyExact⟩
  cases hstep with
  | eqTrue =>
      exact ⟨hpath.1,
        ⟨exactEnv, .bool, hwellExact, hborrowExact, hsafeExact,
          hmapExactApprox, PartialTyStrengthens.reflex,
          ValidPartialValue.bool, WellFormedTy.bool,
          tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_bool⟩⟩
  | eqFalse _hne =>
      exact ⟨hpath.1,
        ⟨exactEnv, .bool, hwellExact, hborrowExact, hsafeExact,
          hmapExactApprox, PartialTyStrengthens.reflex,
          ValidPartialValue.bool, WellFormedTy.bool,
          tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_bool⟩⟩

/--
The relaxed `T-Eq` preservation case reduces to the two operand IHs after
erasing the static ghost slot from the RHS typing.

The RHS is evaluated under `approxLeft`, not under the ghost-extended
environment, because no runtime store slot exists for the ghost name.  The
checked `hRhsErased` bridge records the exact typing fact needed by a recursive
preservation proof.
-/
theorem relaxed_preservation_eq_case
    {store finalStore : ProgramStore}
    {approxIn approxLeft approxOut approxGhost : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {lhs rhs : Term} {lhsTy rhsTy : Ty} {ghost : Name}
    {finalValue : Value} :
    SourceTerm (.eq lhs rhs) →
    ValidRuntimeState store (.eq lhs rhs) →
    ValidStoreTyping store (.eq lhs rhs) typing →
    WellFormedEnv approxIn lifetime →
    RuntimeExactEnvWitness store lifetime approxIn →
    RelaxedTermTyping approxIn typing lifetime lhs lhsTy approxLeft →
    approxLeft.fresh ghost →
    Env.TypeNameFresh approxLeft ghost →
    ghost ∉ Ty.vars lhsTy →
    StoreTyping.TypeNameFresh typing ghost →
    RelaxedTermTyping
      (approxLeft.update ghost { ty := .ty lhsTy, lifetime := lifetime })
      typing lifetime rhs rhsTy approxGhost →
    ¬ Term.Mentions ghost rhs →
    approxOut = approxGhost.erase ghost →
    CopyTy lhsTy →
    CopyTy rhsTy →
    ShapeCompatible approxOut (.ty lhsTy) (.ty rhsTy) →
    (∀ {storeL finalStoreL : ProgramStore} {finalValueL : Value},
      ValidRuntimeState storeL lhs →
      ValidStoreTyping storeL lhs typing →
      WellFormedEnv approxIn lifetime →
      RuntimeExactEnvWitness storeL lifetime approxIn →
      MultiStep storeL lifetime lhs finalStoreL (.val finalValueL) →
      WellFormedEnv approxLeft lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreL lifetime finalValueL
          approxLeft lhsTy) →
    (∀ {storeR finalStoreR : ProgramStore} {finalValueR : Value},
      RelaxedTermTyping approxLeft typing lifetime rhs rhsTy approxOut →
      ValidRuntimeState storeR rhs →
      ValidStoreTyping storeR rhs typing →
      WellFormedEnv approxLeft lifetime →
      RuntimeExactEnvWitness storeR lifetime approxLeft →
      MultiStep storeR lifetime rhs finalStoreR (.val finalValueR) →
      WellFormedEnv approxOut lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreR lifetime finalValueR
          approxOut rhsTy) →
    MultiStep store lifetime (.eq lhs rhs) finalStore (.val finalValue) →
    WellFormedEnv approxOut lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxOut
        .bool := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness hLhs
    hfresh htypeFresh htyFresh hstoreFresh hghostRhs hnotMention henvOut
    hcopyL hcopyR hshape ihLhs ihRhs hmulti
  have hRhsErased :
      RelaxedTermTyping approxLeft typing lifetime rhs rhsTy approxOut := by
    have hRhsErase :
        RelaxedTermTyping approxLeft typing lifetime rhs rhsTy
          (approxGhost.erase ghost) :=
      RelaxedTermTyping.erase_ghost
        (env := approxLeft)
        (ghostSlot := { ty := .ty lhsTy, lifetime := lifetime })
        hfresh htypeFresh
        (by simpa [PartialTy.vars] using htyFresh)
        hstoreFresh hnotMention hghostRhs
    simpa [henvOut] using hRhsErase
  rcases multistep_eq_to_value_inv hmulti with
    ⟨midStore, leftValue, rightStore, rightValue, hleftMulti, hrightMulti,
      hredex⟩
  have htermTyping :
      RelaxedTermTyping approxIn typing lifetime (.eq lhs rhs) .bool
        approxOut :=
    RelaxedTermTyping.eq hLhs hfresh htypeFresh htyFresh hstoreFresh
      hghostRhs hnotMention henvOut hcopyL hcopyR hshape
  have hwellOut : WellFormedEnv approxOut lifetime :=
    (relaxed_typingPreservesWellFormed_of_sourceTerm hsource
      (ValidRuntimeState.validState hvalidRuntime) hwellApproxIn
      (RuntimeExactEnvWitness.safe hwitness) htermTyping).1
  have hsourceLeft : SourceTerm lhs :=
    SourceTerm.eq_lhs hsource
  have hsourceRight : SourceTerm rhs :=
    SourceTerm.eq_rhs hsource
  rcases ihLhs
      (validRuntimeState_of_sourceTerm hsourceLeft hvalidRuntime)
      hvalidStoreTyping.eq_lhs hwellApproxIn hwitness hleftMulti with
    ⟨hwellLeft, hterminalLeft⟩
  have hvalidRight : ValidRuntimeState midStore rhs :=
    validRuntimeState_of_sourceTerm hsourceRight hterminalLeft.1.1
  have hstoreTypingRight : ValidStoreTyping midStore rhs typing :=
    validStoreTyping_sourceTerm_of_validStoreTyping hsourceRight
      hvalidStoreTyping.eq_rhs
  rcases ihRhs hRhsErased hvalidRight hstoreTypingRight hwellLeft
      hterminalLeft.2 hrightMulti with
    ⟨_hwellRight, hterminalRight⟩
  exact ⟨hwellOut, pathSensitive_eq_redex_case hterminalRight hredex⟩

/--
Typed relaxed `T-Eq` preservation case.

The left and right operand IHs may carry branch-specific exact types, but the
comparison redex itself produces an exact Boolean witness.
-/
theorem relaxed_preservation_eq_typed_case
    {store finalStore : ProgramStore}
    {approxIn approxLeft approxOut approxGhost : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {lhs rhs : Term} {lhsTy rhsTy : Ty} {ghost : Name}
    {finalValue : Value} :
    SourceTerm (.eq lhs rhs) →
    ValidRuntimeState store (.eq lhs rhs) →
    ValidStoreTyping store (.eq lhs rhs) typing →
    WellFormedEnv approxIn lifetime →
    RuntimeExactEnvWitness store lifetime approxIn →
    RelaxedTermTyping approxIn typing lifetime lhs lhsTy approxLeft →
    approxLeft.fresh ghost →
    Env.TypeNameFresh approxLeft ghost →
    ghost ∉ Ty.vars lhsTy →
    StoreTyping.TypeNameFresh typing ghost →
    RelaxedTermTyping
      (approxLeft.update ghost { ty := .ty lhsTy, lifetime := lifetime })
      typing lifetime rhs rhsTy approxGhost →
    ¬ Term.Mentions ghost rhs →
    approxOut = approxGhost.erase ghost →
    CopyTy lhsTy →
    CopyTy rhsTy →
    ShapeCompatible approxOut (.ty lhsTy) (.ty rhsTy) →
    (∀ {storeL finalStoreL : ProgramStore} {finalValueL : Value},
      ValidRuntimeState storeL lhs →
      ValidStoreTyping storeL lhs typing →
      WellFormedEnv approxIn lifetime →
      RuntimeExactEnvWitness storeL lifetime approxIn →
      MultiStep storeL lifetime lhs finalStoreL (.val finalValueL) →
      WellFormedEnv approxLeft lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreL lifetime finalValueL
          approxLeft lhsTy) →
    (∀ {storeR finalStoreR : ProgramStore} {finalValueR : Value},
      RelaxedTermTyping approxLeft typing lifetime rhs rhsTy approxOut →
      ValidRuntimeState storeR rhs →
      ValidStoreTyping storeR rhs typing →
      WellFormedEnv approxLeft lifetime →
      RuntimeExactEnvWitness storeR lifetime approxLeft →
      MultiStep storeR lifetime rhs finalStoreR (.val finalValueR) →
      WellFormedEnv approxOut lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreR lifetime finalValueR
          approxOut rhsTy) →
    MultiStep store lifetime (.eq lhs rhs) finalStore (.val finalValue) →
    WellFormedEnv approxOut lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue
        approxOut .bool := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness hLhs
    hfresh htypeFresh htyFresh hstoreFresh hghostRhs hnotMention henvOut
    hcopyL hcopyR hshape ihLhs ihRhs hmulti
  have hRhsErased :
      RelaxedTermTyping approxLeft typing lifetime rhs rhsTy approxOut := by
    have hRhsErase :
        RelaxedTermTyping approxLeft typing lifetime rhs rhsTy
          (approxGhost.erase ghost) :=
      RelaxedTermTyping.erase_ghost
        (env := approxLeft)
        (ghostSlot := { ty := .ty lhsTy, lifetime := lifetime })
        hfresh htypeFresh
        (by simpa [PartialTy.vars] using htyFresh)
        hstoreFresh hnotMention hghostRhs
    simpa [henvOut] using hRhsErase
  rcases multistep_eq_to_value_inv hmulti with
    ⟨midStore, leftValue, rightStore, rightValue, hleftMulti, hrightMulti,
      hredex⟩
  have htermTyping :
      RelaxedTermTyping approxIn typing lifetime (.eq lhs rhs) .bool
        approxOut :=
    RelaxedTermTyping.eq hLhs hfresh htypeFresh htyFresh hstoreFresh
      hghostRhs hnotMention henvOut hcopyL hcopyR hshape
  have hwellOut : WellFormedEnv approxOut lifetime :=
    (relaxed_typingPreservesWellFormed_of_sourceTerm hsource
      (ValidRuntimeState.validState hvalidRuntime) hwellApproxIn
      (RuntimeExactEnvWitness.safe hwitness) htermTyping).1
  have hsourceLeft : SourceTerm lhs :=
    SourceTerm.eq_lhs hsource
  have hsourceRight : SourceTerm rhs :=
    SourceTerm.eq_rhs hsource
  rcases ihLhs
      (validRuntimeState_of_sourceTerm hsourceLeft hvalidRuntime)
      hvalidStoreTyping.eq_lhs hwellApproxIn hwitness hleftMulti with
    ⟨hwellLeft, hterminalLeft⟩
  have hwitnessLeft : RuntimeExactEnvWitness midStore lifetime approxLeft :=
    RuntimeExactTypedValueWitness.to_runtime hterminalLeft.2
  have hvalidRight : ValidRuntimeState midStore rhs :=
    validRuntimeState_of_sourceTerm hsourceRight hterminalLeft.1.1
  have hstoreTypingRight : ValidStoreTyping midStore rhs typing :=
    validStoreTyping_sourceTerm_of_validStoreTyping hsourceRight
      hvalidStoreTyping.eq_rhs
  rcases ihRhs hRhsErased hvalidRight hstoreTypingRight hwellLeft
      hwitnessLeft hrightMulti with
    ⟨_hwellRight, hterminalRight⟩
  exact ⟨hwellOut, pathSensitive_eq_redex_typed_case hterminalRight hredex⟩

/-! ## Declaration frontier -/

/--
Declaration output rebuilt on the exact runtime path.

The shape part is simple: declaration adds the same fresh root on the exact path
and on the approximate continuation environment.  The important exact-side
payloads are `wellOut` and `borrowOut`, especially the latter: it requires the
declared value type to be borrow-safe against the exact path environment, not
against the joined approximation.
-/
structure ExactDeclareTransport (lifetime : Lifetime) (x : Name)
    (approxTy exactTy : Ty) (exactIn approxOut : Env) : Prop where
  fresh : exactIn.fresh x
  typeStrength : PartialTyStrengthens (.ty exactTy) (.ty approxTy)
  wellOut :
    WellFormedEnv
      (exactIn.update x { ty := .ty exactTy, lifetime := lifetime }) lifetime
  borrowOut :
    BorrowSafeEnv
      (exactIn.update x { ty := .ty exactTy, lifetime := lifetime })
  outMap :
    EnvSameShapeStrengthening
      (exactIn.update x { ty := .ty exactTy, lifetime := lifetime })
      approxOut

/--
The remaining typed declaration continuation obligation.

This is analogous to `TypedAssignTransportHook`, but for fresh local
declaration.  The hard part is exact post-declaration well-formedness for the
selected exact initializer type.
-/
def TypedDeclareTransportHook (lifetime : Lifetime) (x : Name)
    (approxTy : Ty) (approxInit approxOut : Env) : Prop :=
  ∀ {storeV storeAfter : ProgramStore} {value finalValueV : Value},
    PathSensitiveTypedTerminalStateSafe storeV lifetime value approxInit
      approxTy →
    ValidRuntimeState storeV (.letMut x (.val value)) →
    Step storeV lifetime (.letMut x (.val value)) storeAfter
      (.val finalValueV) →
    ∀ exactIn exactTy,
      WellFormedEnv exactIn lifetime →
      BorrowSafeEnv exactIn →
      storeV ∼ₛ exactIn →
      EnvSameShapeStrengthening exactIn approxInit →
      PartialTyStrengthens (.ty exactTy) (.ty approxTy) →
      ValidValue storeV value exactTy →
      WellFormedTy exactIn exactTy lifetime →
      TyBorrowSafeAgainstEnv exactIn exactTy →
      ExactDeclareTransport lifetime x approxTy exactTy exactIn approxOut

/--
The non-control-flow assumptions that remain for a top-level typed relaxed
preservation theorem.

Notably, there is no field for `T-If`: the checked relaxed `if` case is already
closed without `BorrowSafeEnv` or `TyBorrowSafeAgainstEnv` on the joined
environment.  The remaining hooks are local continuation obligations for
assignments, declarations, and block exits.
-/
structure RelaxedTypedPreservationHooks : Prop where
  assign {lifetime : Lifetime} {lhs : LVal} {rhsTy : Ty}
    {approxRhs approxOut : Env} :
      TypedAssignTransportHook lifetime lhs rhsTy approxRhs approxOut
  declare {lifetime : Lifetime} {x : Name} {ty : Ty}
    {approxInit approxOut : Env} :
      TypedDeclareTransportHook lifetime x ty approxInit approxOut
  blockResult {blockLifetime parentLifetime : Lifetime}
    {approxEnv : Env} {approxTy : Ty} :
      TypedBlockResultWellFormedHook blockLifetime parentLifetime approxEnv
        approxTy

/--
Build declaration transport from exact local facts and the approximate fresh
update.  This lemma isolates the exact type-safety obligation for the declared
value as `hsafeTyExact`; the declared exact type may be stricter than the
approximate continuation type.
-/
theorem ExactDeclareTransport.of_exact_parts
    {lifetime : Lifetime} {x : Name} {approxTy exactTy : Ty}
    {exactIn approxIn approxOut : Env} :
    EnvSameShapeStrengthening exactIn approxIn →
    approxIn.fresh x →
    approxOut = approxIn.update x { ty := .ty approxTy, lifetime := lifetime } →
    PartialTyStrengthens (.ty exactTy) (.ty approxTy) →
    WellFormedEnv
      (exactIn.update x { ty := .ty exactTy, lifetime := lifetime }) lifetime →
    BorrowSafeEnv exactIn →
    TyBorrowSafeAgainstEnv exactIn exactTy →
    ExactDeclareTransport lifetime x approxTy exactTy exactIn approxOut := by
  intro hmapExactApprox hfreshApprox happroxOut hstrength hwellOut
    hborrowExact hsafeTyExact
  subst happroxOut
  have hfreshExact : exactIn.fresh x :=
    EnvSameShapeStrengthening.source_fresh_of_result_fresh
      hmapExactApprox hfreshApprox
  have hborrowOut :
      BorrowSafeEnv
        (exactIn.update x { ty := .ty exactTy, lifetime := lifetime }) :=
    borrowSafeEnv_update_of_tyBorrowSafeAgainstEnv hborrowExact hsafeTyExact
  have houtMap :
      EnvSameShapeStrengthening
        (exactIn.update x { ty := .ty exactTy, lifetime := lifetime })
        (approxIn.update x { ty := .ty approxTy, lifetime := lifetime }) :=
    EnvSameShapeStrengthening.update_both_fresh_ty_strengthening
      hmapExactApprox hfreshExact hfreshApprox hstrength
  exact
    { fresh := hfreshExact
      typeStrength := hstrength
      wellOut := hwellOut
      borrowOut := hborrowOut
      outMap := houtMap }

/--
Same-type declaration transport is the reflexive instance of the generalized
exact/approx declaration package.
-/
theorem ExactDeclareTransport.of_exact_parts_same_ty
    {lifetime : Lifetime} {x : Name} {ty : Ty}
    {exactIn approxIn approxOut : Env} :
    EnvSameShapeStrengthening exactIn approxIn →
    approxIn.fresh x →
    approxOut = approxIn.update x { ty := .ty ty, lifetime := lifetime } →
    WellFormedEnv
      (exactIn.update x { ty := .ty ty, lifetime := lifetime }) lifetime →
    BorrowSafeEnv exactIn →
    TyBorrowSafeAgainstEnv exactIn ty →
    ExactDeclareTransport lifetime x ty ty exactIn approxOut := by
  intro hmapExactApprox hfreshApprox happroxOut hwellOut hborrowExact
    hsafeTyExact
  exact ExactDeclareTransport.of_exact_parts hmapExactApprox hfreshApprox
    happroxOut PartialTyStrengthens.reflex hwellOut hborrowExact hsafeTyExact

/--
A typed exact runtime value witness supplies the exact declaration type and
exact value validity needed by generalized declaration transport.

The remaining premise is the local exact post-declaration well-formedness fact.
This is intentionally narrower than requiring the approximate joined type to be
borrow-safe against the exact branch environment.
-/
theorem RuntimeExactTypedValueWitness.declare_transport
    {store : ProgramStore} {lifetime : Lifetime} {value : Value}
    {x : Name} {approxTy : Ty} {approxIn approxOut : Env} :
    RuntimeExactTypedValueWitness store lifetime value approxIn approxTy →
    approxIn.fresh x →
    approxOut = approxIn.update x { ty := .ty approxTy, lifetime := lifetime } →
    (∀ exactEnv exactTy,
      WellFormedEnv exactEnv lifetime →
      BorrowSafeEnv exactEnv →
      store ∼ₛ exactEnv →
      EnvSameShapeStrengthening exactEnv approxIn →
      PartialTyStrengthens (.ty exactTy) (.ty approxTy) →
      ValidValue store value exactTy →
      WellFormedTy exactEnv exactTy lifetime →
      TyBorrowSafeAgainstEnv exactEnv exactTy →
      WellFormedEnv
        (exactEnv.update x { ty := .ty exactTy, lifetime := lifetime })
        lifetime) →
    ∃ exactEnv exactTy,
      ValidValue store value exactTy ∧
        ExactDeclareTransport lifetime x approxTy exactTy exactEnv
          approxOut := by
  intro hwitness hfreshApprox happroxOut hwellOutExact
  rcases hwitness with
    ⟨exactEnv, exactTy, hwellExact, hborrowExact, hsafeExact,
      hmapExactApprox, hstrength, hvalidExact, hwellTyExact,
      hsafeTyExact⟩
  have hwellOut :
      WellFormedEnv
        (exactEnv.update x { ty := .ty exactTy, lifetime := lifetime })
        lifetime :=
    hwellOutExact exactEnv exactTy hwellExact hborrowExact hsafeExact
      hmapExactApprox hstrength hvalidExact hwellTyExact hsafeTyExact
  exact ⟨exactEnv, exactTy, hvalidExact,
    ExactDeclareTransport.of_exact_parts hmapExactApprox hfreshApprox
      happroxOut hstrength hwellOut hborrowExact hsafeTyExact⟩

/--
If the current exact runtime witness can be extended by a fresh declaration, the
declaration redex case of relaxed preservation is solved.
-/
theorem pathSensitive_declare_redex_of_exactTransport
    {store store' : ProgramStore} {lifetime : Lifetime}
    {x : Name} {value finalValue : Value} {ty : Ty}
    {approxIn approxOut : Env} :
    RuntimeExactEnvWitness store lifetime approxIn →
    ValidRuntimeState store (.letMut x (.val value)) →
    ValidValue store value ty →
    Step store lifetime (.letMut x (.val value)) store' (.val finalValue) →
    (∀ exactIn,
      WellFormedEnv exactIn lifetime →
      BorrowSafeEnv exactIn →
      store ∼ₛ exactIn →
      EnvSameShapeStrengthening exactIn approxIn →
      ∃ exactTy,
        ValidValue store value exactTy ∧
          ExactDeclareTransport lifetime x ty exactTy exactIn approxOut) →
    PathSensitiveTerminalStateSafe store' lifetime finalValue approxOut .unit := by
  intro hwitness hvalidRuntime hvalidValue hstep htransport
  rcases hwitness with
    ⟨exactIn, hwellExact, hborrowExact, hsafeExact, hmapExactApprox⟩
  rcases htransport exactIn hwellExact hborrowExact hsafeExact
      hmapExactApprox with
    ⟨exactTy, hvalidValueExact, hdecl⟩
  cases hstep with
  | declare hstore' =>
      have hterminalExact :
          TerminalStateSafe store' .unit
            (exactIn.update x { ty := .ty exactTy, lifetime := lifetime })
            .unit :=
        preservation_declare_redex_runtime_of_validValue hsafeExact
          hdecl.fresh hvalidRuntime hvalidValueExact
          (Step.declare (lifetime := lifetime) hstore')
      exact ⟨
        ⟨hterminalExact.1,
          EnvSameShapeStrengthening.safe hdecl.outMap hterminalExact.2.1,
          hterminalExact.2.2⟩,
        ⟨exactIn.update x { ty := .ty exactTy, lifetime := lifetime },
          hdecl.wellOut, hdecl.borrowOut, hterminalExact.2.1,
          hdecl.outMap⟩⟩

/--
Typed declaration redex preservation from exact declaration transport.

The initializer supplies the selected exact value type.  After declaration, the
result value is exactly `unit`, while the selected exact environment has been
extended by the declaration transport.
-/
theorem pathSensitive_declare_redex_typed_of_exactTransport
    {store store' : ProgramStore} {lifetime : Lifetime}
    {x : Name} {value finalValue : Value} {ty : Ty}
    {approxIn approxOut : Env} :
    PathSensitiveTypedTerminalStateSafe store lifetime value approxIn ty →
    ValidRuntimeState store (.letMut x (.val value)) →
    Step store lifetime (.letMut x (.val value)) store' (.val finalValue) →
    (∀ exactIn exactTy,
      WellFormedEnv exactIn lifetime →
      BorrowSafeEnv exactIn →
      store ∼ₛ exactIn →
      EnvSameShapeStrengthening exactIn approxIn →
      PartialTyStrengthens (.ty exactTy) (.ty ty) →
      ValidValue store value exactTy →
      WellFormedTy exactIn exactTy lifetime →
      TyBorrowSafeAgainstEnv exactIn exactTy →
      ExactDeclareTransport lifetime x ty exactTy exactIn approxOut) →
    PathSensitiveTypedTerminalStateSafe store' lifetime finalValue approxOut
      .unit := by
  intro hsafeTyped hvalidRuntime hstep htransport
  rcases hsafeTyped.2 with
    ⟨exactIn, exactTy, hwellExact, hborrowExact, hsafeExact,
      hmapExactApprox, hstrength, hvalidExact, hwellTyExact,
      hsafeTyExact⟩
  have hdecl :
      ExactDeclareTransport lifetime x ty exactTy exactIn approxOut :=
    htransport exactIn exactTy hwellExact hborrowExact hsafeExact
      hmapExactApprox hstrength hvalidExact hwellTyExact hsafeTyExact
  cases hstep with
  | declare hstore' =>
      have hterminalExact :
          TerminalStateSafe store' .unit
            (exactIn.update x { ty := .ty exactTy, lifetime := lifetime })
            .unit :=
        preservation_declare_redex_runtime_of_validValue hsafeExact
          hdecl.fresh hvalidRuntime hvalidExact
          (Step.declare (lifetime := lifetime) hstore')
      exact ⟨
        ⟨hterminalExact.1,
          EnvSameShapeStrengthening.safe hdecl.outMap hterminalExact.2.1,
          hterminalExact.2.2⟩,
        ⟨exactIn.update x { ty := .ty exactTy, lifetime := lifetime },
          .unit, hdecl.wellOut, hdecl.borrowOut, hterminalExact.2.1,
          hdecl.outMap, PartialTyStrengthens.reflex,
          hterminalExact.2.2, WellFormedTy.unit,
          tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit⟩⟩

/--
The full relaxed declaration case reduces to exact declaration transport.

The initializer IH supplies the exact runtime path that produced the declared
value.  The remaining continuation-specific work is exactly `htransport`:
extending that exact environment with the new local and mapping the exact output
back to the static approximate output.
-/
theorem relaxed_preservation_declare_case_of_exactTransport
    {store finalStore : ProgramStore} {approxIn approxInit approxOut : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {term : Term} {ty : Ty} {finalValue : Value} :
    SourceTerm (.letMut x term) →
    ValidRuntimeState store (.letMut x term) →
    ValidStoreTyping store (.letMut x term) typing →
    WellFormedEnv approxIn lifetime →
    RuntimeExactEnvWitness store lifetime approxIn →
    approxIn.fresh x →
    RelaxedTermTyping approxIn typing lifetime term ty approxInit →
    approxInit.fresh x →
    FreshUpdateCoherenceObligations approxInit x ty lifetime →
    approxOut = approxInit.update x { ty := .ty ty, lifetime := lifetime } →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT term →
      ValidStoreTyping storeT term typing →
      WellFormedEnv approxIn lifetime →
      RuntimeExactEnvWitness storeT lifetime approxIn →
      MultiStep storeT lifetime term finalStoreT (.val finalValueT) →
      WellFormedEnv approxInit lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreT lifetime finalValueT
          approxInit ty) →
    (∀ {storeV storeAfter : ProgramStore} {value finalValueV : Value},
      PathSensitiveTerminalStateSafe storeV lifetime value approxInit ty →
      ValidRuntimeState storeV (.letMut x (.val value)) →
      Step storeV lifetime (.letMut x (.val value)) storeAfter
        (.val finalValueV) →
      ∀ exactIn,
        WellFormedEnv exactIn lifetime →
        BorrowSafeEnv exactIn →
        storeV ∼ₛ exactIn →
        EnvSameShapeStrengthening exactIn approxInit →
        ∃ exactTy,
          ValidValue storeV value exactTy ∧
            ExactDeclareTransport lifetime x ty exactTy exactIn approxOut) →
    MultiStep store lifetime (.letMut x term) finalStore (.val finalValue) →
    WellFormedEnv approxOut lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxOut
        .unit := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness
    hfreshIn hinit hfreshOut hcoh henvOut ihInit htransport hmulti
  rcases multistep_declare_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hdeclareStep⟩
  have htermTyping :
      RelaxedTermTyping approxIn typing lifetime (.letMut x term) .unit
        approxOut :=
    RelaxedTermTyping.declare hfreshIn hinit hfreshOut hcoh henvOut
  have hwellOut : WellFormedEnv approxOut lifetime :=
    (relaxed_typingPreservesWellFormed_of_sourceTerm hsource
      (ValidRuntimeState.validState hvalidRuntime) hwellApproxIn
      (RuntimeExactEnvWitness.safe hwitness) htermTyping).1
  rcases ihInit
      (validRuntimeState_declare_inner hvalidRuntime)
      (validStoreTyping_declare_inner hvalidStoreTyping)
      hwellApproxIn hwitness hinnerMulti with
    ⟨_hwellInit, hterminalInit⟩
  have hvalidDeclare :
      ValidRuntimeState midStore (.letMut x (.val value)) :=
    validRuntimeState_declare_value_of_value hterminalInit.1.1
  have hterminalDeclare :
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxOut
        .unit :=
    pathSensitive_declare_redex_of_exactTransport
      hterminalInit.2 hvalidDeclare hterminalInit.1.2.2 hdeclareStep
      (htransport hterminalInit hvalidDeclare hdeclareStep)
  exact ⟨hwellOut, hterminalDeclare⟩

/--
Typed relaxed declaration preservation from exact declaration transport.

The initializer IH carries the selected exact initializer type into the redex;
the redex extends that selected exact environment and resets the selected exact
result type to `unit`.
-/
theorem relaxed_preservation_declare_typed_case_of_exactTransport
    {store finalStore : ProgramStore} {approxIn approxInit approxOut : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {term : Term} {ty : Ty} {finalValue : Value} :
    SourceTerm (.letMut x term) →
    ValidRuntimeState store (.letMut x term) →
    ValidStoreTyping store (.letMut x term) typing →
    WellFormedEnv approxIn lifetime →
    RuntimeExactEnvWitness store lifetime approxIn →
    approxIn.fresh x →
    RelaxedTermTyping approxIn typing lifetime term ty approxInit →
    approxInit.fresh x →
    FreshUpdateCoherenceObligations approxInit x ty lifetime →
    approxOut = approxInit.update x { ty := .ty ty, lifetime := lifetime } →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT term →
      ValidStoreTyping storeT term typing →
      WellFormedEnv approxIn lifetime →
      RuntimeExactEnvWitness storeT lifetime approxIn →
      MultiStep storeT lifetime term finalStoreT (.val finalValueT) →
      WellFormedEnv approxInit lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreT lifetime finalValueT
          approxInit ty) →
    (∀ {storeV storeAfter : ProgramStore} {value finalValueV : Value},
      PathSensitiveTypedTerminalStateSafe storeV lifetime value approxInit
        ty →
      ValidRuntimeState storeV (.letMut x (.val value)) →
      Step storeV lifetime (.letMut x (.val value)) storeAfter
        (.val finalValueV) →
      ∀ exactIn exactTy,
        WellFormedEnv exactIn lifetime →
        BorrowSafeEnv exactIn →
        storeV ∼ₛ exactIn →
        EnvSameShapeStrengthening exactIn approxInit →
        PartialTyStrengthens (.ty exactTy) (.ty ty) →
        ValidValue storeV value exactTy →
        WellFormedTy exactIn exactTy lifetime →
        TyBorrowSafeAgainstEnv exactIn exactTy →
        ExactDeclareTransport lifetime x ty exactTy exactIn approxOut) →
    MultiStep store lifetime (.letMut x term) finalStore (.val finalValue) →
    WellFormedEnv approxOut lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue
        approxOut .unit := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness
    hfreshIn hinit hfreshOut hcoh henvOut ihInit htransport hmulti
  rcases multistep_declare_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hdeclareStep⟩
  have htermTyping :
      RelaxedTermTyping approxIn typing lifetime (.letMut x term) .unit
        approxOut :=
    RelaxedTermTyping.declare hfreshIn hinit hfreshOut hcoh henvOut
  have hwellOut : WellFormedEnv approxOut lifetime :=
    (relaxed_typingPreservesWellFormed_of_sourceTerm hsource
      (ValidRuntimeState.validState hvalidRuntime) hwellApproxIn
      (RuntimeExactEnvWitness.safe hwitness) htermTyping).1
  rcases ihInit
      (validRuntimeState_declare_inner hvalidRuntime)
      (validStoreTyping_declare_inner hvalidStoreTyping)
      hwellApproxIn hwitness hinnerMulti with
    ⟨_hwellInit, hterminalInit⟩
  have hvalidDeclare :
      ValidRuntimeState midStore (.letMut x (.val value)) :=
    validRuntimeState_declare_value_of_value hterminalInit.1.1
  have hterminalDeclare :
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue
        approxOut .unit :=
    pathSensitive_declare_redex_typed_of_exactTransport
      hterminalInit hvalidDeclare hdeclareStep
      (htransport hterminalInit hvalidDeclare hdeclareStep)
  exact ⟨hwellOut, hterminalDeclare⟩

/--
Same as `relaxed_preservation_declare_typed_case_of_exactTransport`, packaged
with the named declaration hook used by the relaxed preservation skeleton.
-/
theorem relaxed_preservation_declare_typed_case_of_hook
    {store finalStore : ProgramStore} {approxIn approxInit approxOut : Env}
    {typing : StoreTyping} {lifetime : Lifetime}
    {x : Name} {term : Term} {ty : Ty} {finalValue : Value} :
    SourceTerm (.letMut x term) →
    ValidRuntimeState store (.letMut x term) →
    ValidStoreTyping store (.letMut x term) typing →
    WellFormedEnv approxIn lifetime →
    RuntimeExactEnvWitness store lifetime approxIn →
    approxIn.fresh x →
    RelaxedTermTyping approxIn typing lifetime term ty approxInit →
    approxInit.fresh x →
    FreshUpdateCoherenceObligations approxInit x ty lifetime →
    approxOut = approxInit.update x { ty := .ty ty, lifetime := lifetime } →
    (∀ {storeT finalStoreT : ProgramStore} {finalValueT : Value},
      ValidRuntimeState storeT term →
      ValidStoreTyping storeT term typing →
      WellFormedEnv approxIn lifetime →
      RuntimeExactEnvWitness storeT lifetime approxIn →
      MultiStep storeT lifetime term finalStoreT (.val finalValueT) →
      WellFormedEnv approxInit lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreT lifetime finalValueT
          approxInit ty) →
    TypedDeclareTransportHook lifetime x ty approxInit approxOut →
    MultiStep store lifetime (.letMut x term) finalStore (.val finalValue) →
    WellFormedEnv approxOut lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue
        approxOut .unit := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness
    hfreshIn hinit hfreshOut hcoh henvOut ihInit htransport hmulti
  exact relaxed_preservation_declare_typed_case_of_exactTransport
    hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness hfreshIn
    hinit hfreshOut hcoh henvOut ihInit htransport hmulti

/--
Direct variable assignment redexes do not need static borrow safety for the
approximate environment to establish ordinary terminal safety.

The only use of the path-sensitive witness is to recover `store ∼ₛ approxIn`.
This is the runtime-safety half of the relaxed continuation story; the stronger
`PathSensitiveTerminalStateSafe` result still needs an exact post-state witness
for subsequent continuation code.
-/
theorem terminal_assign_var_redex_of_runtimeExact
    {store store' : ProgramStore} {lifetime : Lifetime}
    {x : Name} {value finalValue : Value} {rhsTy : Ty}
    {approxIn approxOut : Env} {oldTy : PartialTy}
    {targetLifetime rhsWellLifetime : Lifetime} :
    RuntimeExactEnvWitness store lifetime approxIn →
    WellFormedEnv approxIn lifetime →
    ValidRuntimeState store (.assign (.var x) (.val value)) →
    LValTyping approxIn (.var x) oldTy targetLifetime →
    ShapeCompatible approxIn oldTy (.ty rhsTy) →
    WellFormedTy approxIn rhsTy rhsWellLifetime →
    EnvWrite 0 approxIn (.var x) rhsTy approxOut →
    ¬ WriteProhibited approxOut (.var x) →
    WellFormedEnv approxOut lifetime →
    ValidValue store value rhsTy →
    Step store lifetime (.assign (.var x) (.val value)) store'
      (.val finalValue) →
    TerminalStateSafe store' finalValue approxOut .unit := by
  intro hwitness hwellApprox hvalidRuntime hlval hshape hwellTy hwrite
    hnotWrite hwellOut hvalidValue hstep
  exact preservation_assign_var_step_runtime_of_wellFormed
    hwellApprox (RuntimeExactEnvWitness.safe hwitness) hvalidRuntime
    hlval hshape hwellTy hwrite hnotWrite hwellOut hvalidValue hstep

/--
If the current exact runtime witness can be used to build an
`ExactAssignTransport`, the assignment redex case of relaxed preservation is
already solved.

Thus the remaining preservation problem is not the terminal assignment proof
itself; it is the exact/approx transport supplied by `htransport`.
-/
theorem pathSensitive_assign_redex_of_exactTransport
    {store store' : ProgramStore} {lifetime : Lifetime}
    {lhs : LVal} {value finalValue : Value} {rhsTy : Ty}
    {approxIn approxOut : Env} :
    RuntimeExactEnvWitness store lifetime approxIn →
    ValidRuntimeState store (.assign lhs (.val value)) →
    ValidValue store value rhsTy →
    Step store lifetime (.assign lhs (.val value)) store' (.val finalValue) →
    (∀ exactIn,
      WellFormedEnv exactIn lifetime →
      BorrowSafeEnv exactIn →
      store ∼ₛ exactIn →
      EnvSameShapeStrengthening exactIn approxIn →
      ∃ exactOut oldTy targetLifetime rhsWellLifetime,
        ExactAssignTransport lifetime lhs rhsTy exactIn exactOut approxOut
          oldTy targetLifetime rhsWellLifetime) →
    PathSensitiveTerminalStateSafe store' lifetime finalValue approxOut .unit := by
  intro hwitness hvalidRuntime hvalidValue hstep htransport
  rcases hwitness with
    ⟨exactIn, hwellExact, hborrowExact, hsafeExact, hmapExactApprox⟩
  rcases htransport exactIn hwellExact hborrowExact hsafeExact
      hmapExactApprox with
    ⟨exactOut, oldTy, targetLifetime, rhsWellLifetime, hassign⟩
  have hterminalExact : TerminalStateSafe store' finalValue exactOut .unit :=
    preservation_assign_step_terminal_of_wellFormed
      hwellExact hborrowExact hsafeExact hvalidRuntime
      hassign.lval hassign.shape hassign.wellTy hassign.write
      hassign.ranked hassign.notWrite hassign.wellOut hvalidValue hstep
  exact ⟨
    ⟨hterminalExact.1,
      EnvSameShapeStrengthening.safe hassign.outMap hterminalExact.2.1,
      hterminalExact.2.2⟩,
    ⟨exactOut, hassign.wellOut, hassign.borrowOut,
      hterminalExact.2.1, hassign.outMap⟩⟩

/--
Typed assignment redex preservation from exact assignment transport.

The RHS value may have a stricter selected exact type than the approximate
static RHS type.  The exact assignment transport is therefore built for that
selected exact RHS type; after the redex, the result value is exactly `unit`.
-/
theorem pathSensitive_assign_redex_typed_of_exactTransport
    {store store' : ProgramStore} {lifetime : Lifetime}
    {lhs : LVal} {value finalValue : Value} {approxRhsTy : Ty}
    {approxIn approxOut : Env} :
    PathSensitiveTypedTerminalStateSafe store lifetime value approxIn
      approxRhsTy →
    ValidRuntimeState store (.assign lhs (.val value)) →
    Step store lifetime (.assign lhs (.val value)) store'
      (.val finalValue) →
    (∀ exactIn exactRhsTy,
      WellFormedEnv exactIn lifetime →
      BorrowSafeEnv exactIn →
      store ∼ₛ exactIn →
      EnvSameShapeStrengthening exactIn approxIn →
      PartialTyStrengthens (.ty exactRhsTy) (.ty approxRhsTy) →
      ValidValue store value exactRhsTy →
      WellFormedTy exactIn exactRhsTy lifetime →
      TyBorrowSafeAgainstEnv exactIn exactRhsTy →
      ∃ exactOut oldTy targetLifetime rhsWellLifetime,
        ExactAssignTransport lifetime lhs exactRhsTy exactIn exactOut
          approxOut oldTy targetLifetime rhsWellLifetime) →
    PathSensitiveTypedTerminalStateSafe store' lifetime finalValue approxOut
      .unit := by
  intro hsafeTyped hvalidRuntime hstep htransport
  rcases hsafeTyped.2 with
    ⟨exactIn, exactRhsTy, hwellExact, hborrowExact, hsafeExact,
      hmapExactApprox, hstrength, hvalidExact, hwellTyExact,
      hsafeTyExact⟩
  rcases htransport exactIn exactRhsTy hwellExact hborrowExact hsafeExact
      hmapExactApprox hstrength hvalidExact hwellTyExact hsafeTyExact with
    ⟨exactOut, oldTy, targetLifetime, rhsWellLifetime, hassign⟩
  have hterminalExact : TerminalStateSafe store' finalValue exactOut .unit :=
    preservation_assign_step_terminal_of_wellFormed
      hwellExact hborrowExact hsafeExact hvalidRuntime
      hassign.lval hassign.shape hassign.wellTy hassign.write
      hassign.ranked hassign.notWrite hassign.wellOut hvalidExact hstep
  exact ⟨
    ⟨hterminalExact.1,
      EnvSameShapeStrengthening.safe hassign.outMap hterminalExact.2.1,
      hterminalExact.2.2⟩,
    ⟨exactOut, .unit, hassign.wellOut, hassign.borrowOut,
      hterminalExact.2.1, hassign.outMap, PartialTyStrengthens.reflex,
      hterminalExact.2.2, WellFormedTy.unit,
      tyBorrowSafeAgainstEnv_borrowFree tyBorrowFree_unit⟩⟩

/--
The full relaxed assignment case reduces to exact/approx assignment transport.

The RHS induction hypothesis supplies a path-sensitive exact witness for the
runtime store that reaches `rhs`'s value.  After that, the only remaining
assignment-specific work is `htransport`: rebuilding the assignment typing facts
for the exact runtime environment and mapping its output back to the static
approximation `approxOut`.
-/
theorem relaxed_preservation_assign_case_of_exactTransport
    {store finalStore : ProgramStore} {approxIn approxRhs approxOut : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {finalValue : Value} :
    SourceTerm (.assign lhs rhs) →
    ValidRuntimeState store (.assign lhs rhs) →
    ValidStoreTyping store (.assign lhs rhs) typing →
    WellFormedEnv approxIn lifetime →
    RuntimeExactEnvWitness store lifetime approxIn →
    RelaxedTermTyping approxIn typing lifetime rhs rhsTy approxRhs →
    LValTyping approxRhs lhs oldTy targetLifetime →
    ShapeCompatible approxRhs oldTy (.ty rhsTy) →
    WellFormedTy approxRhs rhsTy targetLifetime →
    EnvWrite 0 approxRhs lhs rhsTy approxOut →
    (∃ φ, LinearizedBy φ approxRhs ∧
      EnvWriteRhsBorrowTargetsBelow φ approxOut rhsTy) →
    Coherent approxOut →
    EnvWriteRhsTargetsWellFormed approxOut rhsTy →
    ¬ WriteProhibited approxOut lhs →
    (∀ {storeR finalStoreR : ProgramStore} {finalValueR : Value},
      ValidRuntimeState storeR rhs →
      ValidStoreTyping storeR rhs typing →
      WellFormedEnv approxIn lifetime →
      RuntimeExactEnvWitness storeR lifetime approxIn →
      MultiStep storeR lifetime rhs finalStoreR (.val finalValueR) →
      WellFormedEnv approxRhs lifetime ∧
        PathSensitiveTerminalStateSafe finalStoreR lifetime finalValueR
          approxRhs rhsTy) →
    (∀ {storeV storeAfter : ProgramStore} {value finalValueV : Value},
      PathSensitiveTerminalStateSafe storeV lifetime value approxRhs rhsTy →
      ValidRuntimeState storeV (.assign lhs (.val value)) →
      Step storeV lifetime (.assign lhs (.val value)) storeAfter
        (.val finalValueV) →
      ∀ exactIn,
        WellFormedEnv exactIn lifetime →
        BorrowSafeEnv exactIn →
        storeV ∼ₛ exactIn →
        EnvSameShapeStrengthening exactIn approxRhs →
        ∃ exactOut oldTy targetLifetime rhsWellLifetime,
          ExactAssignTransport lifetime lhs rhsTy exactIn exactOut approxOut
            oldTy targetLifetime rhsWellLifetime) →
    MultiStep store lifetime (.assign lhs rhs) finalStore (.val finalValue) →
    WellFormedEnv approxOut lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxOut
        .unit := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness
    hRhs hlval hshape hwellTy hwrite hranked hcoh hrhsTargets hnotWrite
    ihRhs htransport hmulti
  rcases multistep_assign_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hassignStep⟩
  have htermTyping :
      RelaxedTermTyping approxIn typing lifetime (.assign lhs rhs) .unit
        approxOut :=
    RelaxedTermTyping.assign hRhs hlval hshape hwellTy hwrite hranked hcoh
      hrhsTargets hnotWrite
  have hwellOut : WellFormedEnv approxOut lifetime :=
    (relaxed_typingPreservesWellFormed_of_sourceTerm hsource
      (ValidRuntimeState.validState hvalidRuntime) hwellApproxIn
      (RuntimeExactEnvWitness.safe hwitness) htermTyping).1
  rcases ihRhs
      (validRuntimeState_assign_inner hvalidRuntime)
      (validStoreTyping_assign_inner hvalidStoreTyping)
      hwellApproxIn hwitness hinnerMulti with
    ⟨_hwellRhs, hterminalRhs⟩
  have hvalidAssign :
      ValidRuntimeState midStore (.assign lhs (.val value)) :=
    validRuntimeState_assign_value_of_value hterminalRhs.1.1
  have hterminalAssign :
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue approxOut
        .unit :=
    pathSensitive_assign_redex_of_exactTransport
      hterminalRhs.2 hvalidAssign hterminalRhs.1.2.2 hassignStep
      (htransport hterminalRhs hvalidAssign hassignStep)
  exact ⟨hwellOut, hterminalAssign⟩

/--
Typed relaxed assignment preservation from exact/approx assignment transport.

This is the typed counterpart of
`relaxed_preservation_assign_case_of_exactTransport`: the RHS IH carries the
selected exact RHS type, and the transport premise rebuilds exact assignment
facts for that exact type.
-/
theorem relaxed_preservation_assign_typed_case_of_exactTransport
    {store finalStore : ProgramStore} {approxIn approxRhs approxOut : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {finalValue : Value} :
    SourceTerm (.assign lhs rhs) →
    ValidRuntimeState store (.assign lhs rhs) →
    ValidStoreTyping store (.assign lhs rhs) typing →
    WellFormedEnv approxIn lifetime →
    RuntimeExactEnvWitness store lifetime approxIn →
    RelaxedTermTyping approxIn typing lifetime rhs rhsTy approxRhs →
    LValTyping approxRhs lhs oldTy targetLifetime →
    ShapeCompatible approxRhs oldTy (.ty rhsTy) →
    WellFormedTy approxRhs rhsTy targetLifetime →
    EnvWrite 0 approxRhs lhs rhsTy approxOut →
    (∃ φ, LinearizedBy φ approxRhs ∧
      EnvWriteRhsBorrowTargetsBelow φ approxOut rhsTy) →
    Coherent approxOut →
    EnvWriteRhsTargetsWellFormed approxOut rhsTy →
    ¬ WriteProhibited approxOut lhs →
    (∀ {storeR finalStoreR : ProgramStore} {finalValueR : Value},
      ValidRuntimeState storeR rhs →
      ValidStoreTyping storeR rhs typing →
      WellFormedEnv approxIn lifetime →
      RuntimeExactEnvWitness storeR lifetime approxIn →
      MultiStep storeR lifetime rhs finalStoreR (.val finalValueR) →
      WellFormedEnv approxRhs lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreR lifetime finalValueR
          approxRhs rhsTy) →
    (∀ {storeV storeAfter : ProgramStore} {value finalValueV : Value},
      PathSensitiveTypedTerminalStateSafe storeV lifetime value approxRhs
        rhsTy →
      ValidRuntimeState storeV (.assign lhs (.val value)) →
      Step storeV lifetime (.assign lhs (.val value)) storeAfter
        (.val finalValueV) →
      ∀ exactIn exactRhsTy,
        WellFormedEnv exactIn lifetime →
        BorrowSafeEnv exactIn →
        storeV ∼ₛ exactIn →
        EnvSameShapeStrengthening exactIn approxRhs →
        PartialTyStrengthens (.ty exactRhsTy) (.ty rhsTy) →
        ValidValue storeV value exactRhsTy →
        WellFormedTy exactIn exactRhsTy lifetime →
        TyBorrowSafeAgainstEnv exactIn exactRhsTy →
        ∃ exactOut oldTy targetLifetime rhsWellLifetime,
          ExactAssignTransport lifetime lhs exactRhsTy exactIn exactOut
            approxOut oldTy targetLifetime rhsWellLifetime) →
    MultiStep store lifetime (.assign lhs rhs) finalStore (.val finalValue) →
    WellFormedEnv approxOut lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue
        approxOut .unit := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness
    hRhs hlval hshape hwellTy hwrite hranked hcoh hrhsTargets hnotWrite
    ihRhs htransport hmulti
  rcases multistep_assign_to_value_inv hmulti with
    ⟨midStore, value, hinnerMulti, hassignStep⟩
  have htermTyping :
      RelaxedTermTyping approxIn typing lifetime (.assign lhs rhs) .unit
        approxOut :=
    RelaxedTermTyping.assign hRhs hlval hshape hwellTy hwrite hranked hcoh
      hrhsTargets hnotWrite
  have hwellOut : WellFormedEnv approxOut lifetime :=
    (relaxed_typingPreservesWellFormed_of_sourceTerm hsource
      (ValidRuntimeState.validState hvalidRuntime) hwellApproxIn
      (RuntimeExactEnvWitness.safe hwitness) htermTyping).1
  rcases ihRhs
      (validRuntimeState_assign_inner hvalidRuntime)
      (validStoreTyping_assign_inner hvalidStoreTyping)
      hwellApproxIn hwitness hinnerMulti with
    ⟨_hwellRhs, hterminalRhs⟩
  have hvalidAssign :
      ValidRuntimeState midStore (.assign lhs (.val value)) :=
    validRuntimeState_assign_value_of_value hterminalRhs.1.1
  have hterminalAssign :
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue
        approxOut .unit :=
    pathSensitive_assign_redex_typed_of_exactTransport
      hterminalRhs hvalidAssign hassignStep
      (htransport hterminalRhs hvalidAssign hassignStep)
  exact ⟨hwellOut, hterminalAssign⟩

/--
Same as `relaxed_preservation_assign_typed_case_of_exactTransport`, packaged
with the named assignment hook used by the relaxed preservation skeleton.
-/
theorem relaxed_preservation_assign_typed_case_of_hook
    {store finalStore : ProgramStore} {approxIn approxRhs approxOut : Env}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    {finalValue : Value} :
    SourceTerm (.assign lhs rhs) →
    ValidRuntimeState store (.assign lhs rhs) →
    ValidStoreTyping store (.assign lhs rhs) typing →
    WellFormedEnv approxIn lifetime →
    RuntimeExactEnvWitness store lifetime approxIn →
    RelaxedTermTyping approxIn typing lifetime rhs rhsTy approxRhs →
    LValTyping approxRhs lhs oldTy targetLifetime →
    ShapeCompatible approxRhs oldTy (.ty rhsTy) →
    WellFormedTy approxRhs rhsTy targetLifetime →
    EnvWrite 0 approxRhs lhs rhsTy approxOut →
    (∃ φ, LinearizedBy φ approxRhs ∧
      EnvWriteRhsBorrowTargetsBelow φ approxOut rhsTy) →
    Coherent approxOut →
    EnvWriteRhsTargetsWellFormed approxOut rhsTy →
    ¬ WriteProhibited approxOut lhs →
    (∀ {storeR finalStoreR : ProgramStore} {finalValueR : Value},
      ValidRuntimeState storeR rhs →
      ValidStoreTyping storeR rhs typing →
      WellFormedEnv approxIn lifetime →
      RuntimeExactEnvWitness storeR lifetime approxIn →
      MultiStep storeR lifetime rhs finalStoreR (.val finalValueR) →
      WellFormedEnv approxRhs lifetime ∧
        PathSensitiveTypedTerminalStateSafe finalStoreR lifetime finalValueR
          approxRhs rhsTy) →
    TypedAssignTransportHook lifetime lhs rhsTy approxRhs approxOut →
    MultiStep store lifetime (.assign lhs rhs) finalStore (.val finalValue) →
    WellFormedEnv approxOut lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue
        approxOut .unit := by
  intro hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness
    hRhs hlval hshape hwellTy hwrite hranked hcoh hrhsTargets hnotWrite
    ihRhs htransport hmulti
  exact relaxed_preservation_assign_typed_case_of_exactTransport
    hsource hvalidRuntime hvalidStoreTyping hwellApproxIn hwitness hRhs hlval
    hshape hwellTy hwrite hranked hcoh hrhsTargets hnotWrite ihRhs
    htransport hmulti

end Paper
end LwRust
