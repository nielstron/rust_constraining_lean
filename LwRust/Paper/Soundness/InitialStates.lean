import LwRust.Paper.Soundness.Theorem_4_12_TypeAndBorrowSafety
import LwRust.Paper.Soundness.Helpers.RuntimeFacts

/-!
# Source-level initial-state corollaries

Concrete specializations of the Section 4 soundness results to source initial
states (empty store, source terms).  These are demonstrations, not part of the
paper-lemma critical path.
-/

namespace LwRust
namespace Paper

open Core

/-- Legacy broad coherence oracle used by the current preservation wrappers.

This is intentionally stronger than the source-level theorem we ultimately want:
it quantifies over arbitrary input environments.  The generated/empty-start
coherence result below is the meaningful target for source programs. -/
def TermTypingOutputsCoherent : Prop :=
  ∀ {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty},
    WellFormedEnv env₁ lifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
    Coherent env₂

def WhileFixpointInvariantsCoherent : Prop :=
  ∀ {envEntry envBack envInv envCond envBody : Env}
    {typing : StoreTyping} {lifetime bodyLifetime : Lifetime}
    {condition body : Term} {bodyTy : Ty},
    WellFormedEnv envEntry lifetime →
    WhileFixpointIteration envEntry typing lifetime bodyLifetime condition body
      envEntry envInv envCond envBody envBack bodyTy →
    EnvJoin envEntry envBack envInv →
    Coherent envInv

def BlockScopedSourceTermList (terms : List Term) : Prop :=
  ∀ term, term ∈ terms → BlockScopedSourceTerm term

def EmptyInitialBlockScopedTermTypingOutputsCoherent : Prop :=
  ∀ {term ty env₂ lifetime},
    BlockScopedSourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    Coherent env₂

def EmptyInitialBlockScopedTermListTypingOutputsCoherent : Prop :=
  ∀ {terms ty env₂ lifetime},
    BlockScopedSourceTermList terms →
    TermListTyping Env.empty StoreTyping.empty lifetime terms ty env₂ →
    Coherent env₂

inductive BlockScopedReachableEnv
    (typing : StoreTyping) (lifetime : Lifetime) : Env → Prop where
  | empty :
      BlockScopedReachableEnv typing lifetime Env.empty
  | step {env₁ env₂ : Env} {term : Term} {ty : Ty} :
      BlockScopedReachableEnv typing lifetime env₁ →
      BlockScopedSourceTerm term →
      TermTyping env₁ typing lifetime term ty env₂ →
      BlockScopedReachableEnv typing lifetime env₂

inductive BlockScopedGeneratedEnv (typing : StoreTyping) : Env → Prop where
  | empty :
      BlockScopedGeneratedEnv typing Env.empty
  | step {env₁ env₂ : Env} {lifetime : Lifetime} {term : Term} {ty : Ty} :
      BlockScopedGeneratedEnv typing env₁ →
      BlockScopedSourceTerm term →
      TermTyping env₁ typing lifetime term ty env₂ →
      BlockScopedGeneratedEnv typing env₂

theorem BlockScopedReachableEnv.to_generated
    {typing : StoreTyping} {lifetime : Lifetime} {env : Env} :
    BlockScopedReachableEnv typing lifetime env →
    BlockScopedGeneratedEnv typing env := by
  intro hreach
  induction hreach with
  | empty =>
      exact BlockScopedGeneratedEnv.empty
  | step hreach hsource htyping ih =>
      exact BlockScopedGeneratedEnv.step ih hsource htyping

def BlockScopedReachableTermTypingOutputsCoherent : Prop :=
  ∀ {env₁ env₂ : Env} {lifetime : Lifetime} {term : Term} {ty : Ty},
    BlockScopedReachableEnv StoreTyping.empty lifetime env₁ →
    BlockScopedSourceTerm term →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    Coherent env₂

def BlockScopedReachableTermTypingOutputsLValCoherent : Prop :=
  ∀ {env₁ env₂ : Env} {lifetime : Lifetime} {term : Term} {ty : Ty},
    BlockScopedReachableEnv StoreTyping.empty lifetime env₁ →
    BlockScopedSourceTerm term →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    LValTypingOutputsCoherent env₂

def BlockScopedReachableTermTypingOutputsPartialLValCoherent : Prop :=
  ∀ {env₁ env₂ : Env} {lifetime : Lifetime} {term : Term} {ty : Ty},
    BlockScopedReachableEnv StoreTyping.empty lifetime env₁ →
    BlockScopedSourceTerm term →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    LValTypingPartialOutputsCoherent env₂

def BlockScopedGeneratedTermTypingOutputsCoherent : Prop :=
  ∀ {env₁ env₂ : Env} {lifetime : Lifetime} {term : Term} {ty : Ty},
    BlockScopedGeneratedEnv StoreTyping.empty env₁ →
    BlockScopedSourceTerm term →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    Coherent env₂

def BlockScopedGeneratedTermTypingOutputsPartialLValCoherent : Prop :=
  ∀ {env₁ env₂ : Env} {lifetime : Lifetime} {term : Term} {ty : Ty},
    BlockScopedGeneratedEnv StoreTyping.empty env₁ →
    BlockScopedSourceTerm term →
    TermTyping env₁ StoreTyping.empty lifetime term ty env₂ →
    LValTypingPartialOutputsCoherent env₂

theorem BlockScopedReachableTermTypingOutputsLValCoherent.coherent :
    BlockScopedReachableTermTypingOutputsLValCoherent →
    BlockScopedReachableTermTypingOutputsCoherent := by
  intro houtputs env₁ env₂ lifetime term ty hreach hsource htyping
  exact LValTypingOutputsCoherent.coherent (houtputs hreach hsource htyping)

theorem BlockScopedReachableTermTypingOutputsPartialLValCoherent.outputs :
    BlockScopedReachableTermTypingOutputsPartialLValCoherent →
    BlockScopedReachableTermTypingOutputsLValCoherent := by
  intro hpartial env₁ env₂ lifetime term ty hreach hsource htyping
  exact (hpartial hreach hsource htyping).outputs

theorem BlockScopedReachableTermTypingOutputsPartialLValCoherent.coherent :
    BlockScopedReachableTermTypingOutputsPartialLValCoherent →
    BlockScopedReachableTermTypingOutputsCoherent := by
  intro hpartial
  exact BlockScopedReachableTermTypingOutputsLValCoherent.coherent
    (BlockScopedReachableTermTypingOutputsPartialLValCoherent.outputs hpartial)

theorem BlockScopedGeneratedTermTypingOutputsPartialLValCoherent.coherent :
    BlockScopedGeneratedTermTypingOutputsPartialLValCoherent →
    BlockScopedGeneratedTermTypingOutputsCoherent := by
  intro hpartial env₁ env₂ lifetime term ty hgenerated hsource htyping
  exact (hpartial hgenerated hsource htyping).coherent

theorem BlockScopedGeneratedTermTypingOutputsCoherent.reachable :
    BlockScopedGeneratedTermTypingOutputsCoherent →
    BlockScopedReachableTermTypingOutputsCoherent := by
  intro hgenerated env₁ env₂ lifetime term ty hreach hsource htyping
  exact hgenerated hreach.to_generated hsource htyping

theorem BlockScopedGeneratedTermTypingOutputsPartialLValCoherent.reachable :
    BlockScopedGeneratedTermTypingOutputsPartialLValCoherent →
    BlockScopedReachableTermTypingOutputsPartialLValCoherent := by
  intro hgenerated env₁ env₂ lifetime term ty hreach hsource htyping
  exact hgenerated hreach.to_generated hsource htyping

theorem BlockScopedGeneratedTermTypingOutputsCoherent.emptyInitialBlockScopedTerm :
    BlockScopedGeneratedTermTypingOutputsCoherent →
    EmptyInitialBlockScopedTermTypingOutputsCoherent := by
  intro hgenerated term ty env₂ lifetime hsource htyping
  exact hgenerated BlockScopedGeneratedEnv.empty hsource htyping

theorem BlockScopedGeneratedTermTypingOutputsPartialLValCoherent.emptyInitialBlockScopedTerm :
    BlockScopedGeneratedTermTypingOutputsPartialLValCoherent →
    EmptyInitialBlockScopedTermTypingOutputsCoherent := by
  intro hgenerated
  exact BlockScopedGeneratedTermTypingOutputsCoherent.emptyInitialBlockScopedTerm
    (BlockScopedGeneratedTermTypingOutputsPartialLValCoherent.coherent
      hgenerated)

theorem TermTypingOutputsCoherent.emptyInitialBlockScopedTerm :
    TermTypingOutputsCoherent →
    EmptyInitialBlockScopedTermTypingOutputsCoherent := by
  intro hcoherentTyping term ty env₂ lifetime _hsource htyping
  exact hcoherentTyping (wellFormedEnv_empty lifetime) htyping

theorem BlockScopedSourceTermList.nil :
    BlockScopedSourceTermList [] := by
  intro term hmem
  cases hmem

theorem BlockScopedSourceTermList.cons {term : Term} {rest : List Term} :
    BlockScopedSourceTerm term →
    BlockScopedSourceTermList rest →
    BlockScopedSourceTermList (term :: rest) := by
  intro hterm hrest candidate hmem
  rcases List.mem_cons.mp hmem with hcandidate | hcandidate
  · subst hcandidate
    exact hterm
  · exact hrest candidate hcandidate

theorem BlockScopedSourceTermList.head {term : Term} {rest : List Term} :
    BlockScopedSourceTermList (term :: rest) →
    BlockScopedSourceTerm term := by
  intro hterms
  exact hterms term (by simp)

theorem BlockScopedSourceTermList.tail {term : Term} {rest : List Term} :
    BlockScopedSourceTermList (term :: rest) →
    BlockScopedSourceTermList rest := by
  intro hterms candidate hmem
  exact hterms candidate (List.mem_cons_of_mem term hmem)

theorem BlockScopedReachableEnv.of_termListTyping_from
    {typing : StoreTyping} {lifetime : Lifetime} {env₁ env₂ : Env}
    {terms : List Term} {ty : Ty} :
    BlockScopedReachableEnv typing lifetime env₁ →
    BlockScopedSourceTermList terms →
    TermListTyping env₁ typing lifetime terms ty env₂ →
    BlockScopedReachableEnv typing lifetime env₂ := by
  intro hreach hsource htyping
  induction terms generalizing env₁ env₂ ty with
  | nil =>
      cases htyping
  | cons term rest ih =>
      cases htyping with
      | singleton hterm =>
          exact BlockScopedReachableEnv.step hreach
            (BlockScopedSourceTermList.head hsource) hterm
      | cons hterm hrest =>
          have hheadReach : BlockScopedReachableEnv typing lifetime _ :=
            BlockScopedReachableEnv.step hreach
              (BlockScopedSourceTermList.head hsource) hterm
          exact ih hheadReach (BlockScopedSourceTermList.tail hsource) hrest

theorem BlockScopedReachableEnv.of_termListTyping
    {typing : StoreTyping} {lifetime : Lifetime} {env₂ : Env}
    {terms : List Term} {ty : Ty} :
    BlockScopedSourceTermList terms →
    TermListTyping Env.empty typing lifetime terms ty env₂ →
    BlockScopedReachableEnv typing lifetime env₂ := by
  intro hsource htyping
  exact BlockScopedReachableEnv.of_termListTyping_from
    BlockScopedReachableEnv.empty hsource htyping

theorem BlockScopedGeneratedEnv.of_termListTyping_from
    {typing : StoreTyping} {lifetime : Lifetime} {env₁ env₂ : Env}
    {terms : List Term} {ty : Ty} :
    BlockScopedGeneratedEnv typing env₁ →
    BlockScopedSourceTermList terms →
    TermListTyping env₁ typing lifetime terms ty env₂ →
    BlockScopedGeneratedEnv typing env₂ := by
  intro hgenerated hsource htyping
  induction terms generalizing env₁ env₂ ty with
  | nil =>
      cases htyping
  | cons term rest ih =>
      cases htyping with
      | singleton hterm =>
          exact BlockScopedGeneratedEnv.step hgenerated
            (BlockScopedSourceTermList.head hsource) hterm
      | cons hterm hrest =>
          have hheadGenerated : BlockScopedGeneratedEnv typing _ :=
            BlockScopedGeneratedEnv.step hgenerated
              (BlockScopedSourceTermList.head hsource) hterm
          exact ih hheadGenerated (BlockScopedSourceTermList.tail hsource) hrest

theorem BlockScopedGeneratedEnv.of_termListTyping
    {typing : StoreTyping} {lifetime : Lifetime} {env₂ : Env}
    {terms : List Term} {ty : Ty} :
    BlockScopedSourceTermList terms →
    TermListTyping Env.empty typing lifetime terms ty env₂ →
    BlockScopedGeneratedEnv typing env₂ := by
  intro hsource htyping
  exact BlockScopedGeneratedEnv.of_termListTyping_from
    BlockScopedGeneratedEnv.empty hsource htyping

theorem BlockScopedReachableTermTypingOutputsCoherent.termList_from :
    BlockScopedReachableTermTypingOutputsCoherent →
    ∀ {env₁ env₂ : Env} {lifetime : Lifetime} {terms : List Term} {ty : Ty},
      BlockScopedReachableEnv StoreTyping.empty lifetime env₁ →
      BlockScopedSourceTermList terms →
      TermListTyping env₁ StoreTyping.empty lifetime terms ty env₂ →
      Coherent env₂ := by
  intro hcoherent env₁ env₂ lifetime terms ty hreach hsource htyping
  induction terms generalizing env₁ env₂ ty with
  | nil =>
      cases htyping
  | cons term rest ih =>
      cases htyping with
      | singleton hterm =>
          exact hcoherent hreach (BlockScopedSourceTermList.head hsource) hterm
      | cons hterm hrest =>
          have hheadReach :
              BlockScopedReachableEnv StoreTyping.empty lifetime _ :=
            BlockScopedReachableEnv.step hreach
              (BlockScopedSourceTermList.head hsource) hterm
          exact ih hheadReach (BlockScopedSourceTermList.tail hsource) hrest

theorem BlockScopedReachableTermTypingOutputsCoherent.emptyInitialTermList :
    BlockScopedReachableTermTypingOutputsCoherent →
    EmptyInitialBlockScopedTermListTypingOutputsCoherent := by
  intro hcoherent terms ty env₂ lifetime hsource htyping
  exact hcoherent.termList_from
    BlockScopedReachableEnv.empty hsource htyping

theorem BlockScopedReachableTermTypingOutputsCoherent.reachableEnv :
    BlockScopedReachableTermTypingOutputsCoherent →
    ∀ {env : Env} {lifetime : Lifetime},
      BlockScopedReachableEnv StoreTyping.empty lifetime env →
      Coherent env := by
  intro hcoherent env lifetime hreach
  induction hreach with
  | empty =>
      exact Coherent.empty
  | step hreach hsource htyping _ih =>
      exact hcoherent hreach hsource htyping

theorem BlockScopedReachableTermTypingOutputsLValCoherent.reachableEnv :
    BlockScopedReachableTermTypingOutputsLValCoherent →
    ∀ {env : Env} {lifetime : Lifetime},
      BlockScopedReachableEnv StoreTyping.empty lifetime env →
      LValTypingOutputsCoherent env := by
  intro houtputs env lifetime hreach
  induction hreach with
  | empty =>
      exact LValTypingOutputsCoherent.empty
  | step hreach hsource htyping _ih =>
      exact houtputs hreach hsource htyping

theorem BlockScopedReachableTermTypingOutputsPartialLValCoherent.reachableEnv :
    BlockScopedReachableTermTypingOutputsPartialLValCoherent →
    ∀ {env : Env} {lifetime : Lifetime},
      BlockScopedReachableEnv StoreTyping.empty lifetime env →
      LValTypingPartialOutputsCoherent env := by
  intro houtputs env lifetime hreach
  induction hreach with
  | empty =>
      exact LValTypingPartialOutputsCoherent.empty
  | step hreach hsource htyping _ih =>
      exact houtputs hreach hsource htyping

theorem BlockScopedGeneratedTermTypingOutputsCoherent.generatedEnv :
    BlockScopedGeneratedTermTypingOutputsCoherent →
    ∀ {env : Env},
      BlockScopedGeneratedEnv StoreTyping.empty env →
      Coherent env := by
  intro houtputs env hgenerated
  induction hgenerated with
  | empty =>
      exact Coherent.empty
  | step hgenerated hsource htyping _ih =>
      exact houtputs hgenerated hsource htyping

theorem BlockScopedGeneratedTermTypingOutputsPartialLValCoherent.generatedEnv :
    BlockScopedGeneratedTermTypingOutputsPartialLValCoherent →
    ∀ {env : Env},
      BlockScopedGeneratedEnv StoreTyping.empty env →
      LValTypingPartialOutputsCoherent env := by
  intro houtputs env hgenerated
  induction hgenerated with
  | empty =>
      exact LValTypingPartialOutputsCoherent.empty
  | step hgenerated hsource htyping _ih =>
      exact houtputs hgenerated hsource htyping

theorem BlockScopedGeneratedTermTypingOutputsCoherent.termList_from :
    BlockScopedGeneratedTermTypingOutputsCoherent →
    ∀ {env₁ env₂ : Env} {lifetime : Lifetime} {terms : List Term} {ty : Ty},
      BlockScopedGeneratedEnv StoreTyping.empty env₁ →
      BlockScopedSourceTermList terms →
      TermListTyping env₁ StoreTyping.empty lifetime terms ty env₂ →
      Coherent env₂ := by
  intro hcoherent env₁ env₂ lifetime terms ty hgenerated hsource htyping
  induction terms generalizing env₁ env₂ ty with
  | nil =>
      cases htyping
  | cons term rest ih =>
      cases htyping with
      | singleton hterm =>
          exact hcoherent hgenerated
            (BlockScopedSourceTermList.head hsource) hterm
      | cons hterm hrest =>
          have hheadGenerated :
              BlockScopedGeneratedEnv StoreTyping.empty _ :=
            BlockScopedGeneratedEnv.step hgenerated
              (BlockScopedSourceTermList.head hsource) hterm
          exact ih hheadGenerated (BlockScopedSourceTermList.tail hsource) hrest

theorem BlockScopedGeneratedTermTypingOutputsPartialLValCoherent.termList_from :
    BlockScopedGeneratedTermTypingOutputsPartialLValCoherent →
    ∀ {env₁ env₂ : Env} {lifetime : Lifetime} {terms : List Term} {ty : Ty},
      BlockScopedGeneratedEnv StoreTyping.empty env₁ →
      BlockScopedSourceTermList terms →
      TermListTyping env₁ StoreTyping.empty lifetime terms ty env₂ →
      LValTypingPartialOutputsCoherent env₂ := by
  intro houtputs env₁ env₂ lifetime terms ty hgenerated hsource htyping
  induction terms generalizing env₁ env₂ ty with
  | nil =>
      cases htyping
  | cons term rest ih =>
      cases htyping with
      | singleton hterm =>
          exact houtputs hgenerated
            (BlockScopedSourceTermList.head hsource) hterm
      | cons hterm hrest =>
          have hheadGenerated :
              BlockScopedGeneratedEnv StoreTyping.empty _ :=
            BlockScopedGeneratedEnv.step hgenerated
              (BlockScopedSourceTermList.head hsource) hterm
          exact ih hheadGenerated (BlockScopedSourceTermList.tail hsource) hrest

theorem BlockScopedGeneratedTermTypingOutputsCoherent.emptyInitialTermList :
    BlockScopedGeneratedTermTypingOutputsCoherent →
    EmptyInitialBlockScopedTermListTypingOutputsCoherent := by
  intro hcoherent terms ty env₂ lifetime hsource htyping
  exact hcoherent.termList_from
    BlockScopedGeneratedEnv.empty hsource htyping

theorem BlockScopedGeneratedTermTypingOutputsPartialLValCoherent.emptyInitialTermList :
    BlockScopedGeneratedTermTypingOutputsPartialLValCoherent →
    EmptyInitialBlockScopedTermListTypingOutputsCoherent := by
  intro hpartial
  exact BlockScopedGeneratedTermTypingOutputsCoherent.emptyInitialTermList
    (BlockScopedGeneratedTermTypingOutputsPartialLValCoherent.coherent hpartial)

/-- Reachable environments inherit the syntactic non-empty borrow-target
invariant from the generated typing rules.  This is one of the invariants needed
by the assignment-coherence proof: it rules out the vacuous `&[]` cases, while
the actual joint target-list typing still comes from the write rule's
`ShapeCompatible` evidence. -/
theorem BlockScopedReachableEnv.borrowTargetsNonempty
    {typing : StoreTyping} {lifetime : Lifetime} {env : Env} :
    StoreTypingTypesBorrowTargetsNonempty typing →
    BlockScopedReachableEnv typing lifetime env →
    EnvTypesBorrowTargetsNonempty env := by
  intro hstore hreach
  induction hreach with
  | empty =>
      exact EnvTypesBorrowTargetsNonempty.empty
  | step _hreach _hsource htyping ih =>
      exact (TermTyping.borrowTargetsNonempty_of_envTypes
        hstore htyping ih).2

theorem BlockScopedReachableEnv.emptyStore_borrowTargetsNonempty
    {lifetime : Lifetime} {env : Env} :
    BlockScopedReachableEnv StoreTyping.empty lifetime env →
    EnvTypesBorrowTargetsNonempty env := by
  intro hreach
  exact hreach.borrowTargetsNonempty
    StoreTypingTypesBorrowTargetsNonempty.empty

theorem BlockScopedGeneratedEnv.borrowTargetsNonempty
    {typing : StoreTyping} {env : Env} :
    StoreTypingTypesBorrowTargetsNonempty typing →
    BlockScopedGeneratedEnv typing env →
    EnvTypesBorrowTargetsNonempty env := by
  intro hstore hgenerated
  induction hgenerated with
  | empty =>
      exact EnvTypesBorrowTargetsNonempty.empty
  | step _hgenerated _hsource htyping ih =>
      exact (TermTyping.borrowTargetsNonempty_of_envTypes
        hstore htyping ih).2

theorem BlockScopedGeneratedEnv.emptyStore_borrowTargetsNonempty
    {env : Env} :
    BlockScopedGeneratedEnv StoreTyping.empty env →
    EnvTypesBorrowTargetsNonempty env := by
  intro hgenerated
  exact hgenerated.borrowTargetsNonempty
    StoreTypingTypesBorrowTargetsNonempty.empty

theorem BlockScopedReachableTermTypingOutputsCoherent.reachableEnv_facts :
    BlockScopedReachableTermTypingOutputsCoherent →
    ∀ {env : Env} {lifetime : Lifetime},
      BlockScopedReachableEnv StoreTyping.empty lifetime env →
      Coherent env ∧ EnvTypesBorrowTargetsNonempty env := by
  intro hcoherent env lifetime hreach
  exact ⟨hcoherent.reachableEnv hreach,
    BlockScopedReachableEnv.emptyStore_borrowTargetsNonempty hreach⟩

theorem emptyInitialTermTyping_borrowTargetsNonempty {term : Term}
    {ty : Ty} {env₂ : Env} {lifetime : Lifetime} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    TyBorrowTargetsNonempty ty ∧ EnvTypesBorrowTargetsNonempty env₂ := by
  intro htyping
  exact TermTyping.borrowTargetsNonempty_of_envTypes
    StoreTypingTypesBorrowTargetsNonempty.empty htyping
    EnvTypesBorrowTargetsNonempty.empty

theorem emptyInitialTermListTyping_borrowTargetsNonempty {terms : List Term}
    {ty : Ty} {env₂ : Env} {lifetime : Lifetime} :
    TermListTyping Env.empty StoreTyping.empty lifetime terms ty env₂ →
    TyBorrowTargetsNonempty ty ∧ EnvTypesBorrowTargetsNonempty env₂ := by
  intro htyping
  exact TermListTyping.borrowTargetsNonempty_of_envTypes
    StoreTypingTypesBorrowTargetsNonempty.empty htyping
    EnvTypesBorrowTargetsNonempty.empty

theorem sourceValue_emptyStoreTyping {store : ProgramStore} {value : Value} :
    SourceValue value →
    ∃ ty, ValueTyping StoreTyping.empty value ty ∧ ValidValue store value ty := by
  intro hsource
  cases value with
  | unit =>
      exact ⟨.unit, ValueTyping.unit, ValidPartialValue.unit⟩
  | int value =>
      exact ⟨.int, ValueTyping.int, ValidPartialValue.int⟩
  | bool value =>
      exact ⟨.bool, ValueTyping.bool, ValidPartialValue.bool⟩
  | ref ref =>
      cases hsource

theorem sourceValue_validValue_of_empty_valueTyping {store : ProgramStore}
    {value : Value} {ty : Ty} :
    SourceValue value →
    ValueTyping StoreTyping.empty value ty →
    ValidValue store value ty := by
  intro hsource htyping
  rcases sourceValue_emptyStoreTyping (store := store) hsource with
    ⟨sourceTy, hsourceTyping, hvalidValue⟩
  have hty : sourceTy = ty :=
    valueTyping_deterministic hsourceTyping htyping
  subst hty
  exact hvalidValue

theorem sourceTerm_validStoreTyping_empty {store : ProgramStore} {term : Term} :
    SourceTerm term →
    ValidStoreTyping store term StoreTyping.empty := by
  intro hsource value hmem
  exact sourceValue_emptyStoreTyping (hsource value hmem)

theorem valueTyping_empty_sourceValue {value : Value} {ty : Ty} :
    ValueTyping StoreTyping.empty value ty →
    SourceValue value := by
  intro htyping
  cases value with
  | unit =>
      trivial
  | int _ =>
      trivial
  | bool _ =>
      trivial
  | ref ref =>
      cases htyping with
      | ref hlookup =>
          simp [StoreTyping.empty] at hlookup

theorem termTyping_empty_sourceTerm {env₂ : Env} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    SourceTerm term := by
  intro htyping
  refine TermTyping.rec
    (motive_1 := fun _env typing lifetime term _ty _env₂ _ =>
      typing = StoreTyping.empty → SourceTerm term)
    (motive_2 := fun _env typing lifetime terms _ty _env₂ _ =>
      typing = StoreTyping.empty → SourceTerm (.block lifetime terms))
    (motive_3 := fun _envEntry _typing _lifetime _bodyLifetime _condition
        _body _current _envInv _envCond _envBody _envBack _bodyTy _ => True)
    ?const ?missing ?copy ?move ?mutBorrow ?immBorrow ?box ?block
    ?declare ?assign ?eq ?ite ?iteDiverging
    ?whileLoopDiverging ?whileLoop ?singleton ?cons ?done ?step
    htyping rfl
  case const =>
    intro _env _typing _lifetime value _ty hvalueTyping htypingEq
    subst htypingEq
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact valueTyping_empty_sourceValue hvalueTyping
  case missing =>
    intro _env _typing _lifetime _ty _hwellTy _hloanFree _htypingEq
      candidate hmem
    simp [termValues] at hmem
  case copy =>
    intro _env _typing _lifetime _valueLifetime _lv _ty _hLv _hcopy _hnotRead
      _htypingEq candidate hmem
    simp [termValues] at hmem
  case move =>
    intro _env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty
      _hLv _hnotWrite _hmove _htypingEq candidate hmem
    simp [termValues] at hmem
  case mutBorrow =>
    intro _env _typing _lifetime _valueLifetime _lv _ty _hLv
      _hmutable _hnotWrite _htypingEq candidate hmem
    simp [termValues] at hmem
  case immBorrow =>
    intro _env _typing _lifetime _valueLifetime _lv _ty _hLv
      _hnotRead _htypingEq candidate hmem
    simp [termValues] at hmem
  case box =>
    intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih htypingEq
      candidate hmem
    exact ih htypingEq candidate (by simpa [termValues] using hmem)
  case block =>
    intro _env₁ _env₂ _env₃ _typing _lifetime blockLifetime _terms _ty
      _hchild _hterms _hwellTy _hdrop ih htypingEq
    exact ih htypingEq
  case declare =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _x _term _ty
      _hfresh _hterm _hfreshOut _hcoh _henv₃ ih htypingEq candidate hmem
    exact ih htypingEq candidate (by simpa [termValues] using hmem)
  case assign =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy
      _rhs _rhsTy _hRhs _hLhsPost _hshape _hwellTy _hwrite _hranked
      _hrhsWF _hnotWrite ih htypingEq candidate hmem
    exact ih htypingEq candidate (by simpa [termValues] using hmem)
  case eq =>
    intro _env₁ _env₂ _env₃ _envGhost _ghost _typing _lifetime _lhs _rhs
      _lhsTy _rhsTy
      _hLhs _hfresh _htypeFresh _htyFresh _hstoreFresh _hghostRhs _hnotMention
      _henvEq
      _hcopyL _hcopyR _hshape ihL ihGhost htypingEq candidate hmem
    simp [termValues] at hmem
    rcases hmem with hleft | hright
    · exact ihL htypingEq candidate hleft
    · exact ihGhost htypingEq candidate hright
  case ite =>
    intro _env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime _condition
      _trueBranch _falseBranch _trueTy _falseTy _joinTy
      _hcondition _htrue _hfalse _hjoin _henvJoin _hsameLeft _hsameRight
      _hwellJoin _hlinear _hborrowSafe _hresultSafe
      ihCondition ihTrue ihFalse htypingEq candidate hmem
    simp [termValues] at hmem
    rcases hmem with hconditionMem | hbranchMem
    · exact ihCondition htypingEq candidate hconditionMem
    · rcases hbranchMem with htrueMem | hfalseMem
      · exact ihTrue htypingEq candidate htrueMem
      · exact ihFalse htypingEq candidate hfalseMem
  case iteDiverging =>
    intro _env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition
      _trueBranch _falseBranch _trueTy _falseTy
      _hcondition _htrue _hfalse _hdiverges
      ihCondition ihTrue ihFalse htypingEq candidate hmem
    simp [termValues] at hmem
    rcases hmem with hconditionMem | hbranchMem
    · exact ihCondition htypingEq candidate hconditionMem
    · rcases hbranchMem with htrueMem | hfalseMem
      · exact ihTrue htypingEq candidate htrueMem
      · exact ihFalse htypingEq candidate hfalseMem
  case whileLoopDiverging =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _bodyLifetime _condition
      _body _bodyTy _hchild _hcond _hbody _hdiverges
      ihCondition ihBody htypingEq candidate hmem
    simp [termValues] at hmem
    rcases hmem with hconditionMem | hbodyMem
    · exact ihCondition htypingEq candidate hconditionMem
    · exact ihBody htypingEq candidate hbodyMem
  case whileLoop =>
    intro _env₁ _envBack _envInv _env₂ _envEntry₂ _env₃ _envEntry₃ _typing
      _lifetime _bodyLifetime _condition _body _bodyTy _bodyEntryTy
      _hchild _hgenerated _hjoin _hss1 _hss2 _hcbwf _hcoh _hlin _hbse
      _hnameFresh _hcondInv _hbodyInv _hwellTy _hdrop _hcondEntry _hbodyEntry
      _ihGenerated ihCondInv ihBodyInv _ihCondEntry htypingEq
      candidate hmem
    simp [termValues] at hmem
    rcases hmem with hconditionMem | hbodyMem
    · exact ihBodyInv htypingEq candidate hconditionMem
    · exact ihCondInv htypingEq candidate hbodyMem
  case singleton =>
    intro _env₁ _env₂ _typing _lifetime _term _ty _hterm ih htypingEq
      candidate hmem
    simp [termValues] at hmem
    exact ih htypingEq candidate hmem
  case cons =>
    intro _env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy
      _hterm _hrest ihHead ihRest htypingEq candidate hmem
    simp [termValues] at hmem
    rcases hmem with hhead | htail
    · exact ihHead htypingEq candidate hhead
    · exact ihRest htypingEq candidate (by simpa [termValues] using htail)
  case done =>
    intros
    trivial
  case step =>
    intros
    trivial

theorem sourceInitialState_valid {term : Term} :
    SourceTerm term →
    ValidState ProgramStore.empty term := by
  intro hsource
  exact ⟨validStore_empty, sourceTerm_validTerm hsource, by
    intro owned _hmem
    exact empty_owns_false owned⟩

theorem sourceInitialRuntimeState_valid {term : Term} :
    SourceTerm term →
    ValidRuntimeState ProgramStore.empty term := by
  intro hsource
  exact ⟨sourceInitialState_valid hsource, storeOwnersAllocated_empty,
    storeOwnerTargetsHeap_empty, heapSlotsRootLifetime_empty,
    sourceTerm_ownerTargetsHeap hsource⟩

theorem emptyInitialRuntimeState_valid_of_typing {env₂ : Env}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ValidRuntimeState ProgramStore.empty term := by
  intro htyping
  exact sourceInitialRuntimeState_valid
    (termTyping_empty_sourceTerm htyping)

theorem emptyInitialValidStoreTyping_of_typing {env₂ : Env}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty := by
  intro htyping
  exact sourceTerm_validStoreTyping_empty
    (store := ProgramStore.empty)
    (termTyping_empty_sourceTerm htyping)

/--
Source-level empty-store programs satisfy the initial hypotheses used by the
Section 4 soundness statements.
-/
theorem sourceInitialSoundnessHypotheses {term : Term} {lifetime : Lifetime} :
    SourceTerm term →
    ValidState ProgramStore.empty term ∧
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
    ProgramStore.empty ∼ₛ Env.empty ∧
    WellFormedEnv Env.empty lifetime ∧
    BorrowSafeEnv Env.empty ∧
    OperationalStoreProgress ProgramStore.empty := by
  intro hsource
  exact ⟨sourceInitialState_valid hsource,
    sourceTerm_validStoreTyping_empty hsource,
    safeAbstraction_empty,
    wellFormedEnv_empty lifetime,
    borrowSafeEnv_empty,
    operationalStoreProgress_empty⟩

/--
Source-level empty-store programs satisfy the mechanised runtime hypotheses,
including the explicit owner-allocation invariant.
-/
theorem sourceInitialRuntimeSoundnessHypotheses {term : Term} {lifetime : Lifetime} :
    SourceTerm term →
    ValidRuntimeState ProgramStore.empty term ∧
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
    ProgramStore.empty ∼ₛ Env.empty ∧
    WellFormedEnv Env.empty lifetime ∧
    BorrowSafeEnv Env.empty ∧
    OperationalStoreProgress ProgramStore.empty := by
  intro hsource
  exact ⟨sourceInitialRuntimeState_valid hsource,
    sourceTerm_validStoreTyping_empty hsource,
    safeAbstraction_empty,
    wellFormedEnv_empty lifetime,
    borrowSafeEnv_empty,
    operationalStoreProgress_empty⟩

/--
Any program typed from the empty environment and empty store typing satisfies the
runtime assumptions required by progress and preservation.
-/
theorem emptyInitialRuntimeSoundnessHypotheses_of_typing {env₂ : Env}
    {lifetime : Lifetime} {term : Term} {ty : Ty} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ValidRuntimeState ProgramStore.empty term ∧
    ValidStoreTyping ProgramStore.empty term StoreTyping.empty ∧
      ProgramStore.empty ∼ₛ Env.empty ∧
      (∀ lifetime, WellFormedEnv Env.empty lifetime) ∧
      BorrowSafeEnv Env.empty ∧
      OperationalStoreProgress ProgramStore.empty ∧
      (∀ env lifetime, StoreTypingRefsWellFormed env StoreTyping.empty lifetime) := by
  intro htyping
  exact ⟨emptyInitialRuntimeState_valid_of_typing htyping,
    emptyInitialValidStoreTyping_of_typing htyping,
      safeAbstraction_empty,
      wellFormedEnv_empty_all,
      borrowSafeEnv_empty,
      operationalStoreProgress_empty,
      by
        intro env lifetime
        exact storeTypingRefsWellFormed_empty env lifetime⟩

/-- **Lemma 4.10.** Empty-store/source-term instance of Progress. -/
theorem sourceInitial_progress {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ProgressResult ProgramStore.empty lifetime term := by
  intro hsource htyping
  exact progress
    (sourceInitialState_valid hsource)
    (sourceTerm_validStoreTyping_empty hsource)
    (wellFormedEnv_empty _)
    safeAbstraction_empty
    operationalStoreProgress_empty
    htyping

/-- **Lemma 4.10.** Empty-store/source-term Progress via `ValidRuntimeState`. -/
theorem sourceInitial_runtime_progress {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ProgressResult ProgramStore.empty lifetime term := by
  intro hsource htyping
  rcases sourceInitialRuntimeSoundnessHypotheses
      (term := term) (lifetime := lifetime) hsource with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, _hwellFormed, _hborrowSafe, hstoreProgress⟩
  exact progress_runtime
    hvalidRuntime
    hvalidStoreTyping
    (wellFormedEnv_empty _)
    hsafe
    hstoreProgress
    htyping

/-- **Lemma 4.10.** Empty-initial Progress from typing alone. -/
theorem emptyInitial_progress {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ProgressResult ProgramStore.empty lifetime term := by
  intro htyping
  rcases emptyInitialRuntimeSoundnessHypotheses_of_typing htyping with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, hwellFormed, _hborrowSafe,
      hstoreProgress, _hrefs⟩
  exact typeAndBorrowProgress hvalidRuntime hvalidStoreTyping (hwellFormed _).2.1
    hsafe hstoreProgress htyping

/--
**Lemma 4.11.** Empty-initial Preservation for terminal multisteps, with all
initial runtime assumptions derived from typing.
-/
theorem emptyInitial_preservation {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} {finalStore : ProgramStore} {finalValue : Value} :
    TermTypingOutputsCoherent →
    WhileFixpointInvariantsCoherent →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hcoherentTyping hcoherentWhileInvariant htyping hmulti
  rcases emptyInitialRuntimeSoundnessHypotheses_of_typing htyping with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, _hwellFormed, hborrowSafe,
      _hstoreProgress, _hrefs⟩
  have hsource : SourceTerm term := termTyping_empty_sourceTerm htyping
  exact preservation hcoherentTyping hcoherentWhileInvariant
    hsource hvalidRuntime hvalidStoreTyping
    (wellFormedEnv_empty lifetime) hborrowSafe hsafe htyping hmulti

/--
**Lemma 4.11.** Empty-initial paper-facing Preservation wrapper.

Unlike the general runtime preservation wrapper, this has no `SourceTerm`
premise: for empty source store typing, `SourceTerm` follows from typability by
`termTyping_empty_sourceTerm`.
-/
theorem lemma_4_11_preservation_emptyInitial {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} {finalStore : ProgramStore} {finalValue : Value} :
    TermTypingOutputsCoherent →
    WhileFixpointInvariantsCoherent →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) →
    TerminalStateSafe finalStore finalValue env₂ ty :=
  emptyInitial_preservation

/--
**Theorem 4.12.** Empty-initial conditional type-and-borrow safety for any term
typed from the empty initial runtime state.
-/
theorem emptyInitial_typeAndBorrowSafety {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    TermTypingOutputsCoherent →
    WhileFixpointInvariantsCoherent →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    TerminatesAsValue ProgramStore.empty lifetime term →
    ProgressResult ProgramStore.empty lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hcoherentTyping hcoherentWhileInvariant htyping hterminates
  rcases emptyInitialRuntimeSoundnessHypotheses_of_typing htyping with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, hwellFormed, hborrowSafe,
      hstoreProgress, _hrefs⟩
  have hsource : SourceTerm term := termTyping_empty_sourceTerm htyping
  exact typeAndBorrowSafety hcoherentTyping hcoherentWhileInvariant
    hsource hvalidRuntime hvalidStoreTyping (hwellFormed _)
    hborrowSafe hsafe hstoreProgress htyping hterminates

/--
**Theorem 4.12.** Empty-initial paper-facing Type and Borrow Safety wrapper.

This is the conditional terminal-safety form specialized to source-initial
programs.  It has no `SourceTerm` premise because `StoreTyping.empty`
typability derives it.
-/
theorem theorem_4_12_typeAndBorrowSafety_emptyInitial {term : Term}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    TermTypingOutputsCoherent →
    WhileFixpointInvariantsCoherent →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    TerminatesAsValue ProgramStore.empty lifetime term →
    ProgressResult ProgramStore.empty lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty :=
  emptyInitial_typeAndBorrowSafety

/-- **Lemma 4.10.** Empty-store/source-term non-terminal step corollary. -/
theorem sourceInitial_progress_step {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step ProgramStore.empty lifetime term store' term' := by
  intro hsource htyping hnotTerminal
  exact (sourceInitial_progress hsource htyping).step_of_not_terminal hnotTerminal

/--
**Lemma 4.10.** Empty-store/source-term non-terminal step corollary via
`ValidRuntimeState`.
-/
theorem sourceInitial_runtime_progress_step {term : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    ¬ Terminal term →
    ∃ store' term', Step ProgramStore.empty lifetime term store' term' := by
  intro hsource htyping hnotTerminal
  exact (sourceInitial_runtime_progress hsource htyping).step_of_not_terminal hnotTerminal

/--
**Lemma 4.11.** Source-initial multistep preservation for a block containing a
source-level value; this is the `R-BlockB` source-level instance.
-/
theorem sourceInitial_blockB_value_multistep_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime blockLifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.block blockLifetime [.val value]) ty env₂ →
    MultiStep ProgramStore.empty lifetime
      (.block blockLifetime [.val value]) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.block blockLifetime [.val value]) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_blockB_value_multistep_runtime_no_slots
    (sourceInitialRuntimeState_valid hsourceTerm)
    safeAbstraction_empty
    htyping
    (empty_no_lifetime_slots blockLifetime)
    (sourceValue_validValue_of_empty_valueTyping hsource
      (blockValueTyping_valueTyping htyping))
    hmulti

/--
**Lemma 4.11.** Source-initial multistep preservation for `box v` with a
source-level value; this is the `R-Box` source-level instance.
-/
theorem sourceInitial_box_value_multistep_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    MultiStep ProgramStore.empty lifetime (.box (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue (.box ty) := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.box (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_box_multistep_runtime
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .box (.val value)) hsourceTerm)
    safeAbstraction_empty
    (sourceInitialRuntimeState_valid hsourceTerm)
    htyping
    hmulti

/--
**Lemma 4.11.** Source-initial multistep preservation for `let mut x = v` with a
source-level value; this is the `R-Declare` source-level instance.
-/
theorem sourceInitial_declare_value_multistep_preservation
    {x : Name} {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {env₃ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    MultiStep ProgramStore.empty lifetime
      (.letMut x (.val value)) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧ finalStore ∼ₛ env₃ ∧
      ValidValue finalStore finalValue .unit := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.letMut x (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_declare_multistep_runtime
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .letMut x (.val value)) hsourceTerm)
    safeAbstraction_empty
    (sourceInitialRuntimeState_valid hsourceTerm)
    htyping
    hmulti

/--
**Lemma 4.11.** Source-level terminal preservation base case, where the program
is already a runtime value and the multistep derivation is reflexive.
-/
theorem sourceInitial_multistep_value_preservation
    {value finalValue : Value} {finalStore : ProgramStore}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    MultiStep ProgramStore.empty lifetime (.val value) finalStore (.val finalValue) →
    ValidRuntimeState finalStore (.val finalValue) ∧
      finalStore ∼ₛ env₂ ∧
      ValidValue finalStore finalValue ty := by
  intro hsource htyping hmulti
  have hsourceTerm : SourceTerm (.val value) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact preservation_multistep_runtime_value
    (sourceInitialRuntimeState_valid hsourceTerm)
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty)
      (term := .val value) hsourceTerm)
    safeAbstraction_empty
    htyping
    hmulti

/-- **Lemma 4.9.** Source-initial borrow invariance through the rule-carried route. -/
theorem sourceInitial_borrowInvariance {term : Term} {env₂ : Env}
    {lifetime : Lifetime} {ty : Ty} :
    TermTypingOutputsCoherent →
    WhileFixpointInvariantsCoherent →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime := by
  intro hcoherentTyping hcoherentWhileInvariant hsource htyping
  exact borrowInvariance_emptyStoreTyping
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    hcoherentTyping hcoherentWhileInvariant
    (wellFormedEnv_empty lifetime)
    safeAbstraction_empty
    htyping

/--
**Theorem 4.12.** Source-initial conditional type-and-borrow safety bridge from
an already-proved preservation conclusion.
-/
theorem sourceInitial_typeAndBorrowSafety_of_preservation
    {term : Term} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    (∀ finalStore finalValue,
      MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) →
      TerminalStateSafe finalStore finalValue env₂ ty) →
    TerminatesAsValue ProgramStore.empty lifetime term →
    ProgressResult ProgramStore.empty lifetime term ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime term finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping hpreservation hterminates
  exact typeAndBorrowSafety_of_preservation
    (sourceInitialRuntimeState_valid hsource)
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty _)
    safeAbstraction_empty
    operationalStoreProgress_empty
    htyping
    hpreservation
    hterminates

/--
**Theorem 4.12.** Source-initial type-and-borrow safety for a source value; the
termination witness is reflexive.
-/
theorem sourceInitial_value_typeAndBorrowSafety
    {value : Value} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.val value) ty env₂ →
    ProgressResult ProgramStore.empty lifetime (.val value) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime (.val value) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.val value) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_multistep_value_preservation hsource htyping hmulti)
    ⟨ProgramStore.empty, value, MultiStep.refl⟩

/--
**Theorem 4.12.** Source-initial type-and-borrow safety for singleton value
blocks, using the `R-BlockB` Lemma 4.11 instance.
-/
theorem sourceInitial_blockB_value_typeAndBorrowSafety
    {value : Value} {lifetime blockLifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime
      (.block blockLifetime [.val value]) ty env₂ →
    ProgressResult ProgramStore.empty lifetime (.block blockLifetime [.val value]) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime
          (.block blockLifetime [.val value]) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.block blockLifetime [.val value]) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  rcases drops_empty_lifetime blockLifetime with ⟨storeAfterDrop, hdrops⟩
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_blockB_value_multistep_preservation hsource htyping hmulti)
    ⟨storeAfterDrop, value,
      MultiStep.trans (Step.blockB (lifetime := lifetime) hdrops) MultiStep.refl⟩

/--
**Theorem 4.12.** Source-initial type-and-borrow safety for `box v`, using the
`R-Box` Lemma 4.11 instance.
-/
theorem sourceInitial_box_value_typeAndBorrowSafety
    {value : Value} {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.box (.val value)) (.box ty) env₂ →
    ProgressResult ProgramStore.empty lifetime (.box (.val value)) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime (.box (.val value)) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₂ (.box ty) := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.box (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  let boxed := ProgramStore.empty.boxAt 0 value
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_box_value_multistep_preservation hsource htyping hmulti)
    ⟨boxed.1, .ref boxed.2,
      MultiStep.trans
        (Step.box (address := 0) (ref := boxed.2)
          (by simp [ProgramStore.fresh, ProgramStore.empty])
          (by simp [boxed]))
        MultiStep.refl⟩

/--
**Theorem 4.12.** Source-initial type-and-borrow safety for `let mut x = v`,
using the `R-Declare` Lemma 4.11 instance.
-/
theorem sourceInitial_declare_value_typeAndBorrowSafety
    {x : Name} {value : Value} {lifetime : Lifetime} {env₃ : Env} :
    SourceValue value →
    TermTyping Env.empty StoreTyping.empty lifetime (.letMut x (.val value)) .unit env₃ →
    ProgressResult ProgramStore.empty lifetime (.letMut x (.val value)) ∧
      ∃ finalStore finalValue,
        MultiStep ProgramStore.empty lifetime (.letMut x (.val value)) finalStore (.val finalValue) ∧
        TerminalStateSafe finalStore finalValue env₃ .unit := by
  intro hsource htyping
  have hsourceTerm : SourceTerm (.letMut x (.val value)) := by
    intro candidate hmem
    simp [termValues] at hmem
    subst hmem
    exact hsource
  exact sourceInitial_typeAndBorrowSafety_of_preservation
    hsourceTerm
    htyping
    (by
      intro finalStore finalValue hmulti
      exact sourceInitial_declare_value_multistep_preservation hsource htyping hmulti)
    ⟨ProgramStore.empty.declare x lifetime value, .unit,
      MultiStep.trans (Step.declare (lifetime := lifetime) rfl) MultiStep.refl⟩

/--
**Lemma 4.9.** Source-initial borrow invariance through the legacy
ranked/fresh-coherence wrapper.

The wrapper no longer requires the old global assignment/declaration
obligations; the typing derivation carries the required local facts.
-/
theorem sourceInitial_borrowInvariance_of_rankedAssign_and_declFreshCoherence
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty}
    :
    TermTypingOutputsCoherent →
    WhileFixpointInvariantsCoherent →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime := by
  intro hcoherentTyping hcoherentWhileInvariant hsource htyping
  exact borrowInvariance_of_rankedAssign_and_declFreshCoherence
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    hcoherentTyping hcoherentWhileInvariant
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    safeAbstraction_empty
    htyping

/-- **Lemma 4.9.** Source-initial borrow invariance through the rule-carried obligation route. -/
theorem sourceInitial_borrowInvariance_of_ruleCarriedObligations
    {term : Term} {env₂ : Env} {lifetime : Lifetime} {ty : Ty} :
    TermTypingOutputsCoherent →
    WhileFixpointInvariantsCoherent →
    SourceTerm term →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    WellFormedEnv env₂ lifetime := by
  intro hcoherentTyping hcoherentWhileInvariant hsource htyping
  exact borrowInvariance_of_ruleCarriedObligations
    (by
      intro env lifetime
      exact storeTypingRefsWellFormed_empty env lifetime)
    hcoherentTyping hcoherentWhileInvariant
    (sourceInitialRuntimeState_valid hsource).1
    (sourceTerm_validStoreTyping_empty (store := ProgramStore.empty) hsource)
    (wellFormedEnv_empty lifetime)
    safeAbstraction_empty
    htyping

/--
**Theorem 4.12, empty-initial terminal-safety form.**  Any term typed from the
empty initial environment and store typing has a safe terminal state whenever
such a terminal execution is supplied.  This no longer derives termination:
generated `missing` syntax is well typed and diverges by self-loop.
-/
theorem emptyInitial_typeAndBorrowSafety_total {term : Term}
    {lifetime : Lifetime} {ty : Ty} {env₂ : Env} :
    TermTypingOutputsCoherent →
    WhileFixpointInvariantsCoherent →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    TerminatesAsValue ProgramStore.empty lifetime term →
    ∃ finalStore finalValue,
      MultiStep ProgramStore.empty lifetime term finalStore
        (.val finalValue) ∧
      TerminalStateSafe finalStore finalValue env₂ ty := by
  intro hcoherentTyping hcoherentWhileInvariant htyping hterminates
  rcases emptyInitialRuntimeSoundnessHypotheses_of_typing htyping with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, hwellFormed, hborrowSafe,
      _hstoreProgress, _hrefs⟩
  have hsource : SourceTerm term := termTyping_empty_sourceTerm htyping
  exact (Soundness.theorem_4_12_typeAndBorrowSafety_total hsource hvalidRuntime hvalidStoreTyping
    hcoherentTyping hcoherentWhileInvariant
    (hwellFormed lifetime) hborrowSafe hsafe
    ProgramStore.finiteSupport_empty htyping hterminates).2

/--
**Unstuckness.**  No state reachable from an empty-initial well-typed program
is stuck: it is terminal or can take a further step.  All invariants are
derived from typability against the empty environment and store typing.
-/
theorem emptyInitial_no_stuck_states {term term' : Term} {lifetime : Lifetime}
    {ty : Ty} {env₂ : Env} {store' : ProgramStore} :
    TermTypingOutputsCoherent →
    WhileFixpointInvariantsCoherent →
    TermTyping Env.empty StoreTyping.empty lifetime term ty env₂ →
    MultiStep ProgramStore.empty lifetime term store' term' →
    Terminal term' ∨
      ∃ store'' term'', Step store' lifetime term' store'' term'' := by
  intro hcoherentTyping hcoherentWhileInvariant htyping hreach
  rcases emptyInitialRuntimeSoundnessHypotheses_of_typing htyping with
    ⟨hvalidRuntime, hvalidStoreTyping, hsafe, hwellFormed, hborrowSafe,
      _hstoreProgress, _hrefs⟩
  have hsource : SourceTerm term := termTyping_empty_sourceTerm htyping
  exact no_stuck_states hcoherentTyping hcoherentWhileInvariant
    hsource hvalidRuntime hvalidStoreTyping
    (hwellFormed lifetime) hborrowSafe hsafe ProgramStore.finiteSupport_empty
    htyping hreach

end Paper
end LwRust
