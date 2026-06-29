import LwRust.Paper.Soundness.Lemma_4_11_Preservation
import LwRust.Paper.Soundness.Helpers.RelaxedInvariant

/-!
# Preservation facts for relaxed control-flow joins

This file isolates the preservation-side part of the relaxed `T-If` question.
The terminal branch-to-join transport does not require `BorrowSafeEnv` for the
joined environment.  Runtime safety can instead be stated with an exact
branch-local environment that strengthens to the joined approximation.
-/

namespace LwRust
namespace Paper

open Core

theorem RuntimeExactEnvWitness.seq_value_drop {store store' : ProgramStore}
    {lifetime : Lifetime} {value : Value} {next : Term} {rest : List Term}
    {approxEnv : Env} :
    RuntimeExactEnvWitness store lifetime approxEnv →
    ValidRuntimeState store (.block lifetime (.val value :: next :: rest)) →
    Drops store [.value value] store' →
    RuntimeExactEnvWitness store' lifetime approxEnv := by
  intro hwitness hvalidRuntime hdrops
  rcases hwitness with
    ⟨exactEnv, hwellExact, hborrowExact, hsafeExact, hmapExactApprox⟩
  exact ⟨exactEnv, hwellExact, hborrowExact,
    safeAbstraction_seq_value_drop hsafeExact hvalidRuntime hwellExact hdrops,
    hmapExactApprox⟩

/--
`R-BlockB` preserves the exact runtime witness through `dropLifetime`.

The only non-mechanical premise is `hwellTyExact`: the result type used by the
block must be well formed in the exact selected environment, not just in the
joined approximation.  This is the same exact/approx transport issue that later
continuation code faces; once supplied, the block/drop part itself is routine.
-/
theorem RuntimeExactEnvWitness.block_value_drop
    {store finalStore : ProgramStore} {lifetime blockLifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} {approxEnv : Env} :
    RuntimeExactEnvWitness store blockLifetime approxEnv →
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    LifetimeChild lifetime blockLifetime →
    ValidValue store value ty →
    (∀ exactEnv,
      WellFormedEnv exactEnv blockLifetime →
      BorrowSafeEnv exactEnv →
      store ∼ₛ exactEnv →
      EnvSameShapeStrengthening exactEnv approxEnv →
      WellFormedTy exactEnv ty lifetime) →
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    RuntimeExactEnvWitness finalStore lifetime
      (approxEnv.dropLifetime blockLifetime) := by
  intro hwitness hvalidRuntime hchild hvalidValue hwellTyExact hmulti
  rcases hwitness with
    ⟨exactEnv, hwellExact, hborrowExact, hsafeExact, hmapExactApprox⟩
  have hwellTy : WellFormedTy exactEnv ty lifetime :=
    hwellTyExact exactEnv hwellExact hborrowExact hsafeExact hmapExactApprox
  have hterminalExact :
      TerminalStateSafe finalStore finalValue
        (exactEnv.dropLifetime blockLifetime) ty :=
    preservation_blockB_value_multistep_runtime_of_runtimeDrop
      hvalidRuntime hsafeExact hchild hwellExact hwellTy hvalidValue hmulti
  rcases Env.dropLifetime_preserves_wellFormed_child
      hchild hwellExact hwellTy rfl with
    ⟨hwellDrop, _hwellTyDrop⟩
  exact ⟨exactEnv.dropLifetime blockLifetime,
    hwellDrop,
    borrowSafeEnv_dropLifetime hborrowExact,
    hterminalExact.2.1,
    EnvSameShapeStrengthening.dropLifetime hmapExactApprox⟩

/--
Path-sensitive terminal safety for relaxed joins: the final value is safe
against the approximate typing environment, while the store still carries an
exact borrow-safe environment witness for later runtime reasoning.
-/
def PathSensitiveTerminalStateSafe (store : ProgramStore) (lifetime : Lifetime)
    (value : Value) (approxEnv : Env) (ty : Ty) : Prop :=
  TerminalStateSafe store value approxEnv ty ∧
    RuntimeExactEnvWitness store lifetime approxEnv

/--
Generic path-sensitive strengthening: the terminal value and the exact runtime
witness both transport along the same same-shape strengthening map.
-/
theorem PathSensitiveTerminalStateSafe.strengthen
    {store : ProgramStore} {lifetime : Lifetime} {value : Value}
    {source result : Env} {sourceTy resultTy : Ty} :
    WellFormedEnv result lifetime →
    EnvSameShapeStrengthening source result →
    PartialTyStrengthens (.ty sourceTy) (.ty resultTy) →
    PathSensitiveTerminalStateSafe store lifetime value source sourceTy →
    PathSensitiveTerminalStateSafe store lifetime value result resultTy := by
  intro hwellResult hmap hstrength hsafePath
  have hsafeResult : store ∼ₛ result :=
    EnvSameShapeStrengthening.safe hmap hsafePath.1.2.1
  exact ⟨
    ⟨hsafePath.1.1, hsafeResult,
      safeStrengthening hwellResult hsafeResult hstrength hsafePath.1.2.2⟩,
    RuntimeExactEnvWitness.strengthen hsafePath.2 hmap⟩

/--
An exact runtime value witness refines the approximate terminal type with the
actual type used by the selected runtime path.

This is the invariant needed after relaxed joins: continuation typing may talk
about an approximate joined type, while the store can still be justified by a
stricter exact branch type that strengthens to it.
-/
def RuntimeExactTypedValueWitness (store : ProgramStore)
    (lifetime : Lifetime) (value : Value) (approxEnv : Env)
    (approxTy : Ty) : Prop :=
  ∃ exactEnv exactTy,
    WellFormedEnv exactEnv lifetime ∧
      BorrowSafeEnv exactEnv ∧
      store ∼ₛ exactEnv ∧
      EnvSameShapeStrengthening exactEnv approxEnv ∧
      PartialTyStrengthens (.ty exactTy) (.ty approxTy) ∧
      ValidValue store value exactTy ∧
      WellFormedTy exactEnv exactTy lifetime ∧
      TyBorrowSafeAgainstEnv exactEnv exactTy

theorem RuntimeExactTypedValueWitness.to_runtime
    {store : ProgramStore} {lifetime : Lifetime} {value : Value}
    {approxEnv : Env} {approxTy : Ty} :
    RuntimeExactTypedValueWitness store lifetime value approxEnv approxTy →
    RuntimeExactEnvWitness store lifetime approxEnv := by
  intro hwitness
  rcases hwitness with
    ⟨exactEnv, _exactTy, hwellExact, hborrowExact, hsafeExact,
      hmapExactApprox, _hstrength, _hvalidExact, _hwellTyExact,
      _hsafeTyExact⟩
  exact ⟨exactEnv, hwellExact, hborrowExact, hsafeExact, hmapExactApprox⟩

/--
Typed path-sensitive terminal safety extends the existing terminal-safety
package with an exact runtime value type.
-/
def PathSensitiveTypedTerminalStateSafe (store : ProgramStore)
    (lifetime : Lifetime) (value : Value) (approxEnv : Env)
    (approxTy : Ty) : Prop :=
  TerminalStateSafe store value approxEnv approxTy ∧
    RuntimeExactTypedValueWitness store lifetime value approxEnv approxTy

/--
The remaining exact-side singleton-block obligation.

At `R-BlockB`, the selected exact value type must be well formed at the parent
lifetime before the exact runtime state is dropped out of the child lifetime.
This is the precise "blocks do not leak variables" condition needed by the
relaxed preservation skeleton.
-/
def TypedBlockResultWellFormedHook (blockLifetime parentLifetime : Lifetime)
    (approxEnv : Env) (approxTy : Ty) : Prop :=
  ∀ {storeV : ProgramStore} {valueV : Value}
      {exactEnv : Env} {exactTy : Ty},
    PathSensitiveTypedTerminalStateSafe storeV blockLifetime valueV approxEnv
      approxTy →
    WellFormedEnv exactEnv blockLifetime →
    BorrowSafeEnv exactEnv →
    storeV ∼ₛ exactEnv →
    EnvSameShapeStrengthening exactEnv approxEnv →
    PartialTyStrengthens (.ty exactTy) (.ty approxTy) →
    ValidValue storeV valueV exactTy →
    WellFormedTy exactEnv exactTy blockLifetime →
    TyBorrowSafeAgainstEnv exactEnv exactTy →
    WellFormedTy exactEnv exactTy parentLifetime

theorem TyBorrowFree.of_strengthens_right {exactTy approxTy : Ty} :
    PartialTyStrengthens (.ty exactTy) (.ty approxTy) →
    TyBorrowFree approxTy →
    TyBorrowFree exactTy := by
  intro hstrength hfree mutable targets hcontainsExact
  have hshape : PartialTy.sameShape (.ty exactTy) (.ty approxTy) := by
    simpa [PartialTy.sameShape] using ty_sameShape_of_strengthens hstrength
  rcases PartialTyContains.mono_strengthens_sameShape hcontainsExact
      hstrength hshape with
    ⟨approxTargets, hcontainsApprox, _hsubset⟩
  exact hfree mutable approxTargets hcontainsApprox

theorem WellFormedTy.of_borrowFree {env : Env} {ty : Ty}
    {lifetime : Lifetime} :
    TyBorrowFree ty →
    WellFormedTy env ty lifetime := by
  intro hfree
  exact wellFormedTy_of_containedBorrowTargets (by
    intro mutable targets hcontains
    exact False.elim (hfree mutable targets hcontains))

theorem TypedBlockResultWellFormedHook.of_borrowFree
    {blockLifetime parentLifetime : Lifetime} {approxEnv : Env}
    {approxTy : Ty} :
    TyBorrowFree approxTy →
    TypedBlockResultWellFormedHook blockLifetime parentLifetime approxEnv
      approxTy := by
  intro hfree _storeV _valueV _exactEnv _exactTy _hsafeValue _hwellExact
    _hborrowExact _hsafeExact _hmapExactApprox hstrength _hvalidExact
    _hwellTyExact _hsafeTyExact
  exact WellFormedTy.of_borrowFree
    (TyBorrowFree.of_strengthens_right hstrength hfree)

theorem PathSensitiveTypedTerminalStateSafe.to_pathSensitive
    {store : ProgramStore} {lifetime : Lifetime} {value : Value}
    {approxEnv : Env} {approxTy : Ty} :
    PathSensitiveTypedTerminalStateSafe store lifetime value approxEnv
      approxTy →
    PathSensitiveTerminalStateSafe store lifetime value approxEnv approxTy := by
  intro hsafe
  exact ⟨hsafe.1, RuntimeExactTypedValueWitness.to_runtime hsafe.2⟩

theorem RuntimeExactTypedValueWitness.strengthen
    {store : ProgramStore} {lifetime : Lifetime} {value : Value}
    {source result : Env} {sourceTy resultTy : Ty} :
    RuntimeExactTypedValueWitness store lifetime value source sourceTy →
    EnvSameShapeStrengthening source result →
    PartialTyStrengthens (.ty sourceTy) (.ty resultTy) →
    RuntimeExactTypedValueWitness store lifetime value result resultTy := by
  intro hwitness hmap hstrength
  rcases hwitness with
    ⟨exactEnv, exactTy, hwellExact, hborrowExact, hsafeExact,
      hmapExactSource, hstrengthExactSource, hvalidExact, hwellTyExact,
      hsafeTyExact⟩
  exact ⟨exactEnv, exactTy, hwellExact, hborrowExact, hsafeExact,
    EnvSameShapeStrengthening.trans hmapExactSource hmap,
    partialTyStrengthens_trans hstrengthExactSource hstrength,
    hvalidExact, hwellTyExact, hsafeTyExact⟩

theorem PathSensitiveTypedTerminalStateSafe.strengthen
    {store : ProgramStore} {lifetime : Lifetime} {value : Value}
    {source result : Env} {sourceTy resultTy : Ty} :
    WellFormedEnv result lifetime →
    EnvSameShapeStrengthening source result →
    PartialTyStrengthens (.ty sourceTy) (.ty resultTy) →
    PathSensitiveTypedTerminalStateSafe store lifetime value source
      sourceTy →
    PathSensitiveTypedTerminalStateSafe store lifetime value result
      resultTy := by
  intro hwellResult hmap hstrength hsafe
  have hpathResult :
      PathSensitiveTerminalStateSafe store lifetime value result resultTy :=
    PathSensitiveTerminalStateSafe.strengthen hwellResult hmap hstrength
      (PathSensitiveTypedTerminalStateSafe.to_pathSensitive hsafe)
  exact ⟨hpathResult.1,
    RuntimeExactTypedValueWitness.strengthen hsafe.2 hmap hstrength⟩

/--
Path-sensitive `R-BlockB`: terminal safety can still be checked against the
approximate post-drop environment, while the exact runtime witness follows the
selected environment through the same lifetime drop.
-/
theorem PathSensitiveTerminalStateSafe.block_value_drop
    {store finalStore : ProgramStore} {lifetime blockLifetime : Lifetime}
    {value finalValue : Value} {ty : Ty} {approxEnv : Env} :
    PathSensitiveTerminalStateSafe store blockLifetime value approxEnv ty →
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv approxEnv blockLifetime →
    WellFormedTy approxEnv ty lifetime →
    (∀ exactEnv,
      WellFormedEnv exactEnv blockLifetime →
      BorrowSafeEnv exactEnv →
      store ∼ₛ exactEnv →
      EnvSameShapeStrengthening exactEnv approxEnv →
      WellFormedTy exactEnv ty lifetime) →
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    PathSensitiveTerminalStateSafe finalStore lifetime finalValue
      (approxEnv.dropLifetime blockLifetime) ty := by
  intro hsafePath hvalidRuntime hchild hwellApprox hwellTyApprox
    hwellTyExact hmulti
  have hterminalApprox :
      TerminalStateSafe finalStore finalValue
        (approxEnv.dropLifetime blockLifetime) ty :=
    preservation_blockB_value_multistep_runtime_of_runtimeDrop
      hvalidRuntime (RuntimeExactEnvWitness.safe hsafePath.2) hchild
      hwellApprox hwellTyApprox hsafePath.1.2.2 hmulti
  exact ⟨hterminalApprox,
    RuntimeExactEnvWitness.block_value_drop hsafePath.2 hvalidRuntime hchild
      hsafePath.1.2.2 hwellTyExact hmulti⟩

/--
Typed path-sensitive `R-BlockB`.

The block/drop step runs against the selected exact environment and selected
exact value type, then weakens that terminal result back to the approximate
post-drop environment and type.  The only extra block-specific obligation is
that the selected exact result type is well formed at the parent lifetime.
-/
theorem PathSensitiveTypedTerminalStateSafe.block_value_drop
    {store finalStore : ProgramStore} {lifetime blockLifetime : Lifetime}
    {value finalValue : Value} {approxTy : Ty} {approxEnv : Env} :
    PathSensitiveTypedTerminalStateSafe store blockLifetime value approxEnv
      approxTy →
    ValidRuntimeState store (.block blockLifetime [.val value]) →
    LifetimeChild lifetime blockLifetime →
    WellFormedEnv approxEnv blockLifetime →
    WellFormedTy approxEnv approxTy lifetime →
    (∀ exactEnv exactTy,
      WellFormedEnv exactEnv blockLifetime →
      BorrowSafeEnv exactEnv →
      store ∼ₛ exactEnv →
      EnvSameShapeStrengthening exactEnv approxEnv →
      PartialTyStrengthens (.ty exactTy) (.ty approxTy) →
      ValidValue store value exactTy →
      WellFormedTy exactEnv exactTy blockLifetime →
      TyBorrowSafeAgainstEnv exactEnv exactTy →
      WellFormedTy exactEnv exactTy lifetime) →
    MultiStep store lifetime (.block blockLifetime [.val value])
      finalStore (.val finalValue) →
    PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue
      (approxEnv.dropLifetime blockLifetime) approxTy := by
  intro hsafeTyped hvalidRuntime hchild hwellApprox hwellTyApprox
    hwellExactParent hmulti
  rcases hsafeTyped.2 with
    ⟨exactEnv, exactTy, hwellExact, hborrowExact, hsafeExact,
      hmapExactApprox, hstrength, hvalidExact, hwellTyExactBlock,
      hsafeTyExact⟩
  have hwellTyExactParent :
      WellFormedTy exactEnv exactTy lifetime :=
    hwellExactParent exactEnv exactTy hwellExact hborrowExact hsafeExact
      hmapExactApprox hstrength hvalidExact hwellTyExactBlock hsafeTyExact
  have hterminalExact :
      TerminalStateSafe finalStore finalValue
        (exactEnv.dropLifetime blockLifetime) exactTy :=
    preservation_blockB_value_multistep_runtime_of_runtimeDrop
      hvalidRuntime hsafeExact hchild hwellExact hwellTyExactParent
      hvalidExact hmulti
  rcases Env.dropLifetime_preserves_wellFormed_child
      hchild hwellExact hwellTyExactParent rfl with
    ⟨hwellExactDrop, hwellTyExactDrop⟩
  rcases Env.dropLifetime_preserves_wellFormed_child
      hchild hwellApprox hwellTyApprox rfl with
    ⟨hwellApproxDrop, _hwellTyApproxDrop⟩
  have hmapDrop :
      EnvSameShapeStrengthening
        (exactEnv.dropLifetime blockLifetime)
        (approxEnv.dropLifetime blockLifetime) :=
    EnvSameShapeStrengthening.dropLifetime hmapExactApprox
  have hsafeApproxDrop :
      finalStore ∼ₛ approxEnv.dropLifetime blockLifetime :=
    EnvSameShapeStrengthening.safe hmapDrop hterminalExact.2.1
  have hvalidApprox :
      ValidValue finalStore finalValue approxTy :=
    safeStrengthening hwellApproxDrop hsafeApproxDrop hstrength
      hterminalExact.2.2
  exact ⟨
    ⟨hterminalExact.1, hsafeApproxDrop, hvalidApprox⟩,
    ⟨exactEnv.dropLifetime blockLifetime, exactTy,
      hwellExactDrop, borrowSafeEnv_dropLifetime hborrowExact,
      hterminalExact.2.1, hmapDrop, hstrength, hterminalExact.2.2,
      hwellTyExactDrop, TyBorrowSafeAgainstEnv.dropLifetime hsafeTyExact⟩⟩

theorem RuntimeExactEnvWitness.join_left {store : ProgramStore}
    {left right join : Env} {lifetime : Lifetime}
    (hjoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join)
    (hwellLeft : WellFormedEnv left lifetime)
    (hborrowLeft : BorrowSafeEnv left)
    (hsafeLeft : store ∼ₛ left) :
    RuntimeExactEnvWitness store lifetime join := by
  exact ⟨left, hwellLeft, hborrowLeft, hsafeLeft,
    EnvJoin.left_sameShapeStrengthening hjoin
      (EnvJoin.branches_sameShape hjoin hsameLeft hsameRight)⟩

theorem RuntimeExactEnvWitness.join_right {store : ProgramStore}
    {left right join : Env} {lifetime : Lifetime}
    (hjoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join)
    (hwellRight : WellFormedEnv right lifetime)
    (hborrowRight : BorrowSafeEnv right)
    (hsafeRight : store ∼ₛ right) :
    RuntimeExactEnvWitness store lifetime join := by
  exact ⟨right, hwellRight, hborrowRight, hsafeRight,
    EnvJoin.right_sameShapeStrengthening hjoin
      (EnvJoin.branches_sameShape hjoin hsameLeft hsameRight)⟩

theorem RuntimeExactEnvWitness.join_left_of_witness {store : ProgramStore}
    {left right join : Env} {lifetime : Lifetime}
    (hjoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join) :
    RuntimeExactEnvWitness store lifetime left →
    RuntimeExactEnvWitness store lifetime join := by
  intro hwitness
  exact hwitness.strengthen
    (EnvJoin.left_sameShapeStrengthening hjoin
      (EnvJoin.branches_sameShape hjoin hsameLeft hsameRight))

theorem RuntimeExactEnvWitness.join_right_of_witness {store : ProgramStore}
    {left right join : Env} {lifetime : Lifetime}
    (hjoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join) :
    RuntimeExactEnvWitness store lifetime right →
    RuntimeExactEnvWitness store lifetime join := by
  intro hwitness
  exact hwitness.strengthen
    (EnvJoin.right_sameShapeStrengthening hjoin
      (EnvJoin.branches_sameShape hjoin hsameLeft hsameRight))

/--
The left branch terminal preservation conclusion can be transported to the
joined environment without assuming `BorrowSafeEnv join`.
-/
theorem terminalStateSafe_ite_join_left {finalStore : ProgramStore}
    {finalValue : Value} {left right join : Env} {lifetime : Lifetime}
    {leftTy rightTy joinTy : Ty}
    (htyJoin : PartialTyJoin (.ty leftTy) (.ty rightTy) (.ty joinTy))
    (henvJoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join)
    (hcoherent : Coherent join)
    (hlinear : Linearizable join)
    (hwellLeft : WellFormedEnv left lifetime)
    (hwellRight : WellFormedEnv right lifetime)
    (hterminalLeft : TerminalStateSafe finalStore finalValue left leftTy) :
    WellFormedEnv join lifetime ∧
      TerminalStateSafe finalStore finalValue join joinTy := by
  have hbranchShape := EnvJoin.branches_sameShape henvJoin hsameLeft hsameRight
  have hcontained := containedBorrowsWellFormed_join henvJoin hsameLeft hsameRight
    hwellLeft.1 hwellRight.1 hcoherent hlinear
  exact TerminalStateSafe.strengthen_join hcontained hcoherent hlinear
    (EnvJoin.lifetimesPreserved_left henvJoin)
    (EnvJoin.left_sameShapeStrengthening henvJoin hbranchShape)
    (PartialTyUnion.left_strengthens htyJoin) hwellLeft hterminalLeft

/--
The right branch terminal preservation conclusion can be transported to the
joined environment without assuming `BorrowSafeEnv join`.
-/
theorem terminalStateSafe_ite_join_right {finalStore : ProgramStore}
    {finalValue : Value} {left right join : Env} {lifetime : Lifetime}
    {leftTy rightTy joinTy : Ty}
    (htyJoin : PartialTyJoin (.ty leftTy) (.ty rightTy) (.ty joinTy))
    (henvJoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join)
    (hcoherent : Coherent join)
    (hlinear : Linearizable join)
    (hwellLeft : WellFormedEnv left lifetime)
    (hwellRight : WellFormedEnv right lifetime)
    (hterminalRight : TerminalStateSafe finalStore finalValue right rightTy) :
    WellFormedEnv join lifetime ∧
      TerminalStateSafe finalStore finalValue join joinTy := by
  have hbranchShape := EnvJoin.branches_sameShape henvJoin hsameLeft hsameRight
  have hcontained := containedBorrowsWellFormed_join henvJoin hsameLeft hsameRight
    hwellLeft.1 hwellRight.1 hcoherent hlinear
  exact TerminalStateSafe.strengthen_join hcontained hcoherent hlinear
    (EnvJoin.lifetimesPreserved_right henvJoin)
    (EnvJoin.right_sameShapeStrengthening henvJoin hbranchShape)
    (PartialTyUnion.right_strengthens htyJoin) hwellRight hterminalRight

theorem terminalStateSafe_ite_join_left_path {finalStore : ProgramStore}
    {finalValue : Value} {left right join : Env} {lifetime : Lifetime}
    {leftTy rightTy joinTy : Ty}
    (htyJoin : PartialTyJoin (.ty leftTy) (.ty rightTy) (.ty joinTy))
    (henvJoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join)
    (hcoherent : Coherent join)
    (hlinear : Linearizable join)
    (hwellLeft : WellFormedEnv left lifetime)
    (hwellRight : WellFormedEnv right lifetime)
    (hterminalLeft :
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue left leftTy) :
    WellFormedEnv join lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue join joinTy := by
  rcases terminalStateSafe_ite_join_left htyJoin henvJoin hsameLeft hsameRight
      hcoherent hlinear hwellLeft hwellRight hterminalLeft.1 with
    ⟨hwellJoin, hterminalJoin⟩
  exact ⟨hwellJoin, hterminalJoin,
    RuntimeExactEnvWitness.join_left_of_witness henvJoin hsameLeft hsameRight
      hterminalLeft.2⟩

theorem terminalStateSafe_ite_join_right_path {finalStore : ProgramStore}
    {finalValue : Value} {left right join : Env} {lifetime : Lifetime}
    {leftTy rightTy joinTy : Ty}
    (htyJoin : PartialTyJoin (.ty leftTy) (.ty rightTy) (.ty joinTy))
    (henvJoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join)
    (hcoherent : Coherent join)
    (hlinear : Linearizable join)
    (hwellLeft : WellFormedEnv left lifetime)
    (hwellRight : WellFormedEnv right lifetime)
    (hterminalRight :
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue right rightTy) :
    WellFormedEnv join lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue join joinTy := by
  rcases terminalStateSafe_ite_join_right htyJoin henvJoin hsameLeft hsameRight
      hcoherent hlinear hwellLeft hwellRight hterminalRight.1 with
    ⟨hwellJoin, hterminalJoin⟩
  exact ⟨hwellJoin, hterminalJoin,
    RuntimeExactEnvWitness.join_right_of_witness henvJoin hsameLeft hsameRight
      hterminalRight.2⟩

/--
Typed left-branch join transport.

The exact value type is supplied by the selected branch and is then weakened to
the joined approximation.  The joined environment still does not need to be
borrow-safe.
-/
theorem terminalStateSafe_ite_join_left_typed {finalStore : ProgramStore}
    {finalValue : Value} {left right join : Env} {lifetime : Lifetime}
    {leftTy rightTy joinTy : Ty}
    (htyJoin : PartialTyJoin (.ty leftTy) (.ty rightTy) (.ty joinTy))
    (henvJoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join)
    (hcoherent : Coherent join)
    (hlinear : Linearizable join)
    (hwellLeft : WellFormedEnv left lifetime)
    (hwellRight : WellFormedEnv right lifetime)
    (hterminalLeft :
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue left
        leftTy) :
    WellFormedEnv join lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue join
        joinTy := by
  rcases terminalStateSafe_ite_join_left htyJoin henvJoin hsameLeft hsameRight
      hcoherent hlinear hwellLeft hwellRight hterminalLeft.1 with
    ⟨hwellJoin, _hterminalJoin⟩
  have hbranchShape :=
    EnvJoin.branches_sameShape henvJoin hsameLeft hsameRight
  exact ⟨hwellJoin,
    PathSensitiveTypedTerminalStateSafe.strengthen hwellJoin
      (EnvJoin.left_sameShapeStrengthening henvJoin hbranchShape)
      (PartialTyUnion.left_strengthens htyJoin) hterminalLeft⟩

/--
Typed right-branch join transport.

This is the symmetric selected-branch version of
`terminalStateSafe_ite_join_left_typed`.
-/
theorem terminalStateSafe_ite_join_right_typed {finalStore : ProgramStore}
    {finalValue : Value} {left right join : Env} {lifetime : Lifetime}
    {leftTy rightTy joinTy : Ty}
    (htyJoin : PartialTyJoin (.ty leftTy) (.ty rightTy) (.ty joinTy))
    (henvJoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join)
    (hcoherent : Coherent join)
    (hlinear : Linearizable join)
    (hwellLeft : WellFormedEnv left lifetime)
    (hwellRight : WellFormedEnv right lifetime)
    (hterminalRight :
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue right
        rightTy) :
    WellFormedEnv join lifetime ∧
      PathSensitiveTypedTerminalStateSafe finalStore lifetime finalValue join
        joinTy := by
  rcases terminalStateSafe_ite_join_right htyJoin henvJoin hsameLeft hsameRight
      hcoherent hlinear hwellLeft hwellRight hterminalRight.1 with
    ⟨hwellJoin, _hterminalJoin⟩
  have hbranchShape :=
    EnvJoin.branches_sameShape henvJoin hsameLeft hsameRight
  exact ⟨hwellJoin,
    PathSensitiveTypedTerminalStateSafe.strengthen hwellJoin
      (EnvJoin.right_sameShapeStrengthening henvJoin hbranchShape)
      (PartialTyUnion.right_strengthens htyJoin) hterminalRight⟩

/--
Left-branch join transport plus the exact-runtime witness.  This is the
path-sensitive replacement for a static `BorrowSafeEnv join` conclusion.
-/
theorem terminalStateSafe_ite_join_left_exact {finalStore : ProgramStore}
    {finalValue : Value} {left right join : Env} {lifetime : Lifetime}
    {leftTy rightTy joinTy : Ty}
    (htyJoin : PartialTyJoin (.ty leftTy) (.ty rightTy) (.ty joinTy))
    (henvJoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join)
    (hcoherent : Coherent join)
    (hlinear : Linearizable join)
    (hwellLeft : WellFormedEnv left lifetime)
    (hwellRight : WellFormedEnv right lifetime)
    (hborrowLeft : BorrowSafeEnv left)
    (hterminalLeft : TerminalStateSafe finalStore finalValue left leftTy) :
    WellFormedEnv join lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue join joinTy := by
  rcases terminalStateSafe_ite_join_left htyJoin henvJoin hsameLeft hsameRight
      hcoherent hlinear hwellLeft hwellRight hterminalLeft with
    ⟨hwellJoin, hterminalJoin⟩
  exact ⟨hwellJoin, hterminalJoin,
    RuntimeExactEnvWitness.join_left henvJoin hsameLeft hsameRight
      hwellLeft hborrowLeft hterminalLeft.2.1⟩

/--
Right-branch join transport plus the exact-runtime witness.  This is the
path-sensitive replacement for a static `BorrowSafeEnv join` conclusion.
-/
theorem terminalStateSafe_ite_join_right_exact {finalStore : ProgramStore}
    {finalValue : Value} {left right join : Env} {lifetime : Lifetime}
    {leftTy rightTy joinTy : Ty}
    (htyJoin : PartialTyJoin (.ty leftTy) (.ty rightTy) (.ty joinTy))
    (henvJoin : EnvJoin left right join)
    (hsameLeft : EnvJoinSameShape left join)
    (hsameRight : EnvJoinSameShape right join)
    (hcoherent : Coherent join)
    (hlinear : Linearizable join)
    (hwellLeft : WellFormedEnv left lifetime)
    (hwellRight : WellFormedEnv right lifetime)
    (hborrowRight : BorrowSafeEnv right)
    (hterminalRight : TerminalStateSafe finalStore finalValue right rightTy) :
    WellFormedEnv join lifetime ∧
      PathSensitiveTerminalStateSafe finalStore lifetime finalValue join joinTy := by
  rcases terminalStateSafe_ite_join_right htyJoin henvJoin hsameLeft hsameRight
      hcoherent hlinear hwellLeft hwellRight hterminalRight with
    ⟨hwellJoin, hterminalJoin⟩
  exact ⟨hwellJoin, hterminalJoin,
    RuntimeExactEnvWitness.join_right henvJoin hsameLeft hsameRight
      hwellRight hborrowRight hterminalRight.2.1⟩

end Paper
end LwRust
