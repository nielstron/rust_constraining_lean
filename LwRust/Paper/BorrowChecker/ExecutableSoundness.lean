import LwRust.Paper.BorrowChecker.Executable

/-!
Soundness of the executable borrow/type checker.
-/

namespace LwRust
namespace Paper

open Core

/--
Proof-facing bridge for a particular checker run: the executable checker
computes the expected type and finite output environment, and the same input
and output environments support the declarative `TermTyping` judgment consumed
by progress and preservation.
-/
def CheckedTermTypingWitness (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (term : Term)
    (expectedTy : Ty) (expectedEnv : FiniteEnv) : Prop :=
  checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv = true ∧
    TermTyping env.toEnv typing lifetime term expectedTy expectedEnv.toEnv

namespace CheckedTermTypingWitness

theorem checked {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv} :
    CheckedTermTypingWitness fuel env typing lifetime term expectedTy expectedEnv →
      checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv = true :=
  And.left

theorem typing {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv} :
    CheckedTermTypingWitness fuel env typing lifetime term expectedTy expectedEnv →
      TermTyping env.toEnv typing lifetime term expectedTy expectedEnv.toEnv :=
  And.right

theorem typable {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv} :
    CheckedTermTypingWitness fuel env typing lifetime term expectedTy expectedEnv →
      ∃ env₂ ty, TermTyping env.toEnv typing lifetime term ty env₂ := by
  intro h
  exact ⟨expectedEnv.toEnv, expectedTy, h.typing⟩

end CheckedTermTypingWitness

/--
Type-level certificate form of `CheckedTermTypingWitness`.

Unlike the proposition above, this can be returned under `Option`: the executable
boolean at that boundary is simply whether a certified witness was constructed.
-/
structure CertifiedTermCheck (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (term : Term)
    (expectedTy : Ty) (expectedEnv : FiniteEnv) : Type where
  checked :
    checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv = true
  typing :
    TermTyping env.toEnv typing lifetime term expectedTy expectedEnv.toEnv

namespace CertifiedTermCheck

def ofWitness {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (witness :
      CheckedTermTypingWitness fuel env typing lifetime term expectedTy expectedEnv) :
    CertifiedTermCheck fuel env typing lifetime term expectedTy expectedEnv :=
  { checked := witness.checked
    typing := witness.typing }

def toWitness {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate :
      CertifiedTermCheck fuel env typing lifetime term expectedTy expectedEnv) :
    CheckedTermTypingWitness fuel env typing lifetime term expectedTy expectedEnv :=
  ⟨certificate.checked, certificate.typing⟩

def found? {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate? :
      Option (CertifiedTermCheck fuel env typing lifetime term expectedTy expectedEnv)) :
    Bool :=
  certificate?.isSome

theorem sound {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate :
      CertifiedTermCheck fuel env typing lifetime term expectedTy expectedEnv) :
    TermTyping env.toEnv typing lifetime term expectedTy expectedEnv.toEnv :=
  certificate.typing

theorem check_matches {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate :
      CertifiedTermCheck fuel env typing lifetime term expectedTy expectedEnv) :
    checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv = true :=
  certificate.checked

theorem typable {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate :
      CertifiedTermCheck fuel env typing lifetime term expectedTy expectedEnv) :
    ∃ env₂ ty, TermTyping env.toEnv typing lifetime term ty env₂ := by
  exact ⟨expectedEnv.toEnv, expectedTy, certificate.typing⟩

def const {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {value : Value} {ty : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.val value) ty env = true)
    (valueTyping : ValueTyping typing value ty) :
    CertifiedTermCheck fuel env typing lifetime (.val value) ty env :=
  { checked := checked
    typing := TermTyping.const valueTyping }

def copy {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.copy lv) ty env = true)
    (lvalTyping : LValTyping env.toEnv lv (.ty ty) valueLifetime)
    (copyTy : CopyTy ty)
    (notReadProhibited : ¬ ReadProhibited env.toEnv lv) :
    CertifiedTermCheck fuel env typing lifetime (.copy lv) ty env :=
  { checked := checked
    typing := TermTyping.copy lvalTyping copyTy notReadProhibited }

def mutBorrow {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.borrow true lv)
        (.borrow true [lv]) env = true)
    (lvalTyping : LValTyping env.toEnv lv (.ty ty) valueLifetime)
    (mutable : Mutable env.toEnv lv)
    (notWriteProhibited : ¬ WriteProhibited env.toEnv lv) :
    CertifiedTermCheck fuel env typing lifetime (.borrow true lv)
      (.borrow true [lv]) env :=
  { checked := checked
    typing := TermTyping.mutBorrow lvalTyping mutable notWriteProhibited }

def immBorrow {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime valueLifetime : Lifetime} {lv : LVal} {ty : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.borrow false lv)
        (.borrow false [lv]) env = true)
    (lvalTyping : LValTyping env.toEnv lv (.ty ty) valueLifetime)
    (notReadProhibited : ¬ ReadProhibited env.toEnv lv) :
    CertifiedTermCheck fuel env typing lifetime (.borrow false lv)
      (.borrow false [lv]) env :=
  { checked := checked
    typing := TermTyping.immBorrow lvalTyping notReadProhibited }

def declare {fuel : Nat} {env initEnv outEnv : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {name : Name}
    {initialiser : Term} {ty : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.letMut name initialiser)
        .unit outEnv = true)
    (freshIn : env.toEnv.fresh name)
    (initialiserCert :
      CertifiedTermCheck fuel env typing lifetime initialiser ty initEnv)
    (freshOut : initEnv.toEnv.fresh name)
    (coherence :
      FreshUpdateCoherenceObligations initEnv.toEnv name ty lifetime)
    (outEq :
      outEnv.toEnv =
        initEnv.toEnv.update name { ty := .ty ty, lifetime := lifetime }) :
    CertifiedTermCheck fuel env typing lifetime (.letMut name initialiser)
      .unit outEnv :=
  { checked := checked
    typing :=
      TermTyping.declare freshIn initialiserCert.typing freshOut coherence
        outEq }

def assign {fuel : Nat} {env rhsEnv outEnv : FiniteEnv}
    {typing : StoreTyping} {lifetime targetLifetime : Lifetime}
    {lhs : LVal} {oldTy : PartialTy} {rhs : Term} {rhsTy : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.assign lhs rhs) .unit
        outEnv = true)
    (lhsBefore : LValTyping env.toEnv lhs oldTy targetLifetime)
    (rhsCert : CertifiedTermCheck fuel env typing lifetime rhs rhsTy rhsEnv)
    (lhsAfter : LValTyping rhsEnv.toEnv lhs oldTy targetLifetime)
    (shape : ShapeCompatible rhsEnv.toEnv oldTy (.ty rhsTy))
    (wellFormed : WellFormedTy rhsEnv.toEnv rhsTy targetLifetime)
    (write : EnvWrite 0 rhsEnv.toEnv lhs rhsTy outEnv.toEnv)
    (below :
      ∃ φ, LinearizedBy φ rhsEnv.toEnv ∧
        EnvWriteRhsBorrowTargetsBelow φ outEnv.toEnv rhsTy)
    (coherence :
      EnvWriteCoherenceObligations rhsEnv.toEnv outEnv.toEnv (LVal.base lhs))
    (contained : ContainedBorrowsWellFormed outEnv.toEnv)
    (notWriteProhibited : ¬ WriteProhibited outEnv.toEnv lhs) :
    CertifiedTermCheck fuel env typing lifetime (.assign lhs rhs) .unit outEnv :=
  { checked := checked
    typing :=
      TermTyping.assign lhsBefore rhsCert.typing lhsAfter shape
        wellFormed write below coherence contained notWriteProhibited }

def equal {fuel : Nat} {env lhsEnv rhsEnv ghostEnv : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {lhs rhs : Term}
    {lhsTy rhsTy ghostRhsTy : Ty} {ghost : Name}
    (checked :
      checkTermMatches? fuel env typing lifetime (.eq lhs rhs) .bool
        rhsEnv = true)
    (lhsCert : CertifiedTermCheck fuel env typing lifetime lhs lhsTy lhsEnv)
    (freshGhost : lhsEnv.toEnv.fresh ghost)
    (ghostCert :
      CertifiedTermCheck fuel
        (lhsEnv.update ghost { ty := .ty lhsTy, lifetime := lifetime })
        typing lifetime rhs ghostRhsTy ghostEnv)
    (rhsCert : CertifiedTermCheck fuel lhsEnv typing lifetime rhs rhsTy rhsEnv)
    (lhsCopy : CopyTy lhsTy)
    (rhsCopy : CopyTy rhsTy)
    (shape : ShapeCompatible rhsEnv.toEnv (.ty lhsTy) (.ty rhsTy)) :
    CertifiedTermCheck fuel env typing lifetime (.eq lhs rhs) .bool rhsEnv :=
  { checked := checked
    typing :=
      TermTyping.eq (ghost := ghost) lhsCert.typing freshGhost
        (by simpa [FiniteEnv.toEnv_update] using ghostCert.typing)
        rhsCert.typing lhsCopy rhsCopy shape }

def ite {fuel : Nat} {env conditionEnv trueEnv falseEnv joinEnv : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime}
    {condition trueBranch falseBranch : Term} {trueTy falseTy joinTy : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime
        (.ite condition trueBranch falseBranch) joinTy joinEnv = true)
    (conditionCert :
      CertifiedTermCheck fuel env typing lifetime condition .bool conditionEnv)
    (trueCert :
      CertifiedTermCheck fuel conditionEnv typing lifetime trueBranch trueTy
        trueEnv)
    (falseCert :
      CertifiedTermCheck fuel conditionEnv typing lifetime falseBranch falseTy
        falseEnv)
    (typeJoin : PartialTyJoin (.ty trueTy) (.ty falseTy) (.ty joinTy))
    (envJoin : EnvJoin trueEnv.toEnv falseEnv.toEnv joinEnv.toEnv)
    (trueSameShape : EnvJoinSameShape trueEnv.toEnv joinEnv.toEnv)
    (falseSameShape : EnvJoinSameShape falseEnv.toEnv joinEnv.toEnv)
    (wellFormed : WellFormedTy joinEnv.toEnv joinTy lifetime)
    (contained : ContainedBorrowsWellFormed joinEnv.toEnv)
    (coherent : Coherent joinEnv.toEnv)
    (linearizable : Linearizable joinEnv.toEnv) :
    CertifiedTermCheck fuel env typing lifetime
      (.ite condition trueBranch falseBranch) joinTy joinEnv :=
  { checked := checked
    typing :=
      TermTyping.ite conditionCert.typing trueCert.typing falseCert.typing
        typeJoin envJoin trueSameShape falseSameShape wellFormed contained
        coherent linearizable }

end CertifiedTermCheck

/--
Proof-carrying rejection certificate.

This is intentionally separate from `checkTermFails?`: the boolean says the
executable checker produced a finite rule-premise failure rather than an
unknown result, while `notyping` is the logical non-typability proof.  A failed
checker run alone is not used as a completeness theorem.
-/
structure CertifiedTermReject (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (term : Term) : Type where
  checked : checkTermFails? fuel env typing lifetime term = true
  notyping :
    ¬ ∃ ty outEnv, TermTyping env.toEnv typing lifetime term ty outEnv

namespace CertifiedTermReject

def found? {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term}
    (certificate? :
      Option (CertifiedTermReject fuel env typing lifetime term)) : Bool :=
  certificate?.isSome

theorem checkedFailure {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term}
    (certificate : CertifiedTermReject fuel env typing lifetime term) :
    checkTermFails? fuel env typing lifetime term = true :=
  certificate.checked

theorem sound {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term}
    (certificate : CertifiedTermReject fuel env typing lifetime term) :
    ¬ ∃ ty outEnv, TermTyping env.toEnv typing lifetime term ty outEnv :=
  certificate.notyping

end CertifiedTermReject

/-- Proof-carrying counterpart of `checkTermList?` for block bodies. -/
structure CertifiedTermListCheck (fuel : Nat) (env : FiniteEnv)
    (typing : StoreTyping) (lifetime : Lifetime) (terms : List Term)
    (expectedTy : Ty) (expectedEnv : FiniteEnv) : Type where
  checked :
    checkTermListMatches? fuel env typing lifetime terms expectedTy expectedEnv =
      true
  typing :
    TermListTyping env.toEnv typing lifetime terms expectedTy expectedEnv.toEnv

namespace CertifiedTermListCheck

def singleton {fuel : Nat} {env outEnv : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (checked :
      checkTermListMatches? fuel env typing lifetime [term] ty outEnv = true)
    (termCert : CertifiedTermCheck fuel env typing lifetime term ty outEnv) :
    CertifiedTermListCheck fuel env typing lifetime [term] ty outEnv :=
  { checked := checked
    typing := TermListTyping.singleton termCert.typing }

def cons {fuel : Nat} {env midEnv outEnv : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {rest : List Term} {termTy finalTy : Ty}
    (checked :
      checkTermListMatches? fuel env typing lifetime (term :: rest) finalTy
        outEnv = true)
    (headCert : CertifiedTermCheck fuel env typing lifetime term termTy midEnv)
    (restCert :
      CertifiedTermListCheck fuel midEnv typing lifetime rest finalTy outEnv) :
    CertifiedTermListCheck fuel env typing lifetime (term :: rest) finalTy
      outEnv :=
  { checked := checked
    typing := TermListTyping.cons headCert.typing restCert.typing }

theorem sound {fuel : Nat} {env : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {terms : List Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate :
      CertifiedTermListCheck fuel env typing lifetime terms expectedTy
        expectedEnv) :
    TermListTyping env.toEnv typing lifetime terms expectedTy
      expectedEnv.toEnv :=
  certificate.typing

end CertifiedTermListCheck

namespace CertifiedTermCheck

def block {fuel : Nat} {env bodyEnv outEnv : FiniteEnv}
    {typing : StoreTyping} {lifetime blockLifetime : Lifetime}
    {terms : List Term} {ty : Ty}
    (checked :
      checkTermMatches? fuel env typing lifetime (.block blockLifetime terms)
        ty outEnv = true)
    (child : LifetimeChild lifetime blockLifetime)
    (bodyCert :
      CertifiedTermListCheck fuel env typing blockLifetime terms ty bodyEnv)
    (wellFormed : WellFormedTy bodyEnv.toEnv ty lifetime)
    (dropEq : outEnv.toEnv = bodyEnv.toEnv.dropLifetime blockLifetime) :
    CertifiedTermCheck fuel env typing lifetime (.block blockLifetime terms) ty
      outEnv :=
  { checked := checked
    typing := TermTyping.block child bodyCert.typing wellFormed dropEq }

end CertifiedTermCheck

/--
Project facts from a proof-carrying borrow-checking certificate.

Bare `borrow_check` proves closed `borrowCheck` goals by running the executable
checker with the default public-example fuel and applying its soundness bridge.
It also proves proof-carrying accepted, failed, and unknown witness goals from
the corresponding executable booleans.  `borrow_check[n]` uses explicit fuel.
`borrow_check[n, result]` proves exact closed `TermTyping` goals from a
computed `CheckResult`.  `borrow_check[n, inEnv, outEnv]` proves exact
term-level `TermTyping` or `TermListTyping` goals by running
`checkTermMatches?` or `checkTermListMatches?` from the finite input
environment to the finite output environment, for empty store typings and
goals whose environments are written as `inEnv.toEnv` and `outEnv.toEnv`.
`borrow_check using cert` exposes the proof stored in a proof-carrying
certificate.
-/
syntax (name := borrow_check_tactic) "borrow_check" (" using " term)? : tactic
syntax (name := borrow_check_fuel_tactic) "borrow_check" "[" term "]" : tactic
syntax (name := borrow_check_result_tactic)
  "borrow_check" "[" term ", " term "]" : tactic
syntax (name := borrow_check_term_result_tactic)
  "borrow_check" "[" term ", " term ", " term "]" : tactic

/--
Proof-carrying finite checker failure.

This records only the executable failure classification: the program checker
returned a non-unknown error message.  It deliberately does not contain a
non-typability proof; use `CertifiedBorrowReject` for logical rejection.
-/
structure CertifiedBorrowFailure (fuel : Nat) (term : Term) : Type where
  checked : borrowCheckFailed? fuel term = true

namespace CertifiedBorrowFailure

def found? {fuel : Nat} {term : Term}
    (certificate? : Option (CertifiedBorrowFailure fuel term)) : Bool :=
  certificate?.isSome

theorem checkedFailure {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowFailure fuel term) :
    borrowCheckFailed? fuel term = true :=
  certificate.checked

theorem checkerError {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowFailure fuel term) :
    ∃ message,
      checkProgram? fuel term = .error message ∧
        checkerErrorUnknown? message = false := by
  have h := certificate.checked
  unfold borrowCheckFailed? borrowCheckVerdict? at h
  cases hcheck : checkProgram? fuel term with
  | ok result =>
      simp [hcheck] at h
  | error message =>
      cases hunknown : checkerErrorUnknown? message
      · exact ⟨message, rfl, hunknown⟩
      · simp [hcheck, hunknown] at h

theorem checkedFailure_of_found? {fuel : Nat} {term : Term}
    {certificate? : Option (CertifiedBorrowFailure fuel term)} :
    found? certificate? = true → borrowCheckFailed? fuel term = true := by
  cases certificate? with
  | none =>
      simp [found?]
  | some certificate =>
      intro _h
      exact certificate.checkedFailure

end CertifiedBorrowFailure

/--
Proof-carrying unknown checker result.

This records that the executable checker returned an error classified as
unknown, such as fuel exhaustion or an inference limitation.
-/
structure CertifiedBorrowUnknown (fuel : Nat) (term : Term) : Type where
  checked : borrowUnknown? fuel term = true

namespace CertifiedBorrowUnknown

def found? {fuel : Nat} {term : Term}
    (certificate? : Option (CertifiedBorrowUnknown fuel term)) : Bool :=
  certificate?.isSome

theorem checkedUnknown {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowUnknown fuel term) :
    borrowUnknown? fuel term = true :=
  certificate.checked

theorem checkerError {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowUnknown fuel term) :
    ∃ message,
      checkProgram? fuel term = .error message ∧
        checkerErrorUnknown? message = true := by
  have h := certificate.checked
  unfold borrowUnknown? borrowCheckVerdict? at h
  cases hcheck : checkProgram? fuel term with
  | ok result =>
      simp [hcheck] at h
  | error message =>
      cases hunknown : checkerErrorUnknown? message
      · simp [hcheck, hunknown] at h
      · exact ⟨message, rfl, hunknown⟩

theorem checkedUnknown_of_found? {fuel : Nat} {term : Term}
    {certificate? : Option (CertifiedBorrowUnknown fuel term)} :
    found? certificate? = true → borrowUnknown? fuel term = true := by
  cases certificate? with
  | none =>
      simp [found?]
  | some certificate =>
      intro _h
      exact certificate.checkedUnknown

end CertifiedBorrowUnknown

def certifyBorrowFailure? (fuel : Nat) (term : Term) :
    Option (CertifiedBorrowFailure fuel term) :=
  if hchecked : borrowCheckFailed? fuel term = true then
    some { checked := hchecked }
  else
    none

theorem certifyBorrowFailure?_found_iff {fuel : Nat} {term : Term} :
    CertifiedBorrowFailure.found? (certifyBorrowFailure? fuel term) = true ↔
      borrowCheckFailed? fuel term = true := by
  unfold CertifiedBorrowFailure.found? certifyBorrowFailure?
  by_cases hchecked : borrowCheckFailed? fuel term = true <;> simp [hchecked]

/--
Proof-level reflection target for finite checker failures.

This is the failed-verdict analogue of `borrowCheckWitness`: it says the
checker produced a non-unknown failure witness, not that the program is
logically untypable.
-/
def borrowCheckFailureWitness (fuel : Nat) (term : Term) : Prop :=
  Nonempty (CertifiedBorrowFailure fuel term)

theorem borrowCheckFailed?_eq_true_iff_witness {fuel : Nat} {term : Term} :
    borrowCheckFailed? fuel term = true ↔
      borrowCheckFailureWitness fuel term := by
  constructor
  · intro hfailed
    exact ⟨{ checked := hfailed }⟩
  · intro hwitness
    rcases hwitness with ⟨certificate⟩
    exact certificate.checkedFailure

theorem borrowCheckFailureWitness_checked {fuel : Nat} {term : Term} :
    borrowCheckFailureWitness fuel term →
      borrowCheckFailed? fuel term = true := by
  intro hwitness
  exact (borrowCheckFailed?_eq_true_iff_witness).2 hwitness

theorem borrowCheckFailureWitness_of_certifyBorrowFailure?
    {fuel : Nat} {term : Term} :
    CertifiedBorrowFailure.found? (certifyBorrowFailure? fuel term) = true →
      borrowCheckFailureWitness fuel term := by
  intro hfound
  exact (borrowCheckFailed?_eq_true_iff_witness).1
    ((certifyBorrowFailure?_found_iff).1 hfound)

def certifyBorrowUnknown? (fuel : Nat) (term : Term) :
    Option (CertifiedBorrowUnknown fuel term) :=
  if hchecked : borrowUnknown? fuel term = true then
    some { checked := hchecked }
  else
    none

theorem certifyBorrowUnknown?_found_iff {fuel : Nat} {term : Term} :
    CertifiedBorrowUnknown.found? (certifyBorrowUnknown? fuel term) = true ↔
      borrowUnknown? fuel term = true := by
  unfold CertifiedBorrowUnknown.found? certifyBorrowUnknown?
  by_cases hchecked : borrowUnknown? fuel term = true <;> simp [hchecked]

/--
Proof-level reflection target for unknown checker results.
-/
def borrowUnknownWitness (fuel : Nat) (term : Term) : Prop :=
  Nonempty (CertifiedBorrowUnknown fuel term)

theorem borrowUnknown?_eq_true_iff_witness {fuel : Nat} {term : Term} :
    borrowUnknown? fuel term = true ↔ borrowUnknownWitness fuel term := by
  constructor
  · intro hunknown
    exact ⟨{ checked := hunknown }⟩
  · intro hwitness
    rcases hwitness with ⟨certificate⟩
    exact certificate.checkedUnknown

theorem borrowUnknownWitness_checked {fuel : Nat} {term : Term} :
    borrowUnknownWitness fuel term → borrowUnknown? fuel term = true := by
  intro hwitness
  exact (borrowUnknown?_eq_true_iff_witness).2 hwitness

theorem borrowUnknownWitness_of_certifyBorrowUnknown?
    {fuel : Nat} {term : Term} :
    CertifiedBorrowUnknown.found? (certifyBorrowUnknown? fuel term) = true →
      borrowUnknownWitness fuel term := by
  intro hfound
  exact (borrowUnknown?_eq_true_iff_witness).1
    ((certifyBorrowUnknown?_found_iff).1 hfound)

namespace CertifiedTermReject

theorem borrowReject {fuel : Nat} {term : Term}
    (certificate :
      CertifiedTermReject fuel FiniteEnv.empty StoreTyping.empty Lifetime.root
        term) :
    LwRust.Paper.borrowReject term :=
  borrowReject_of_no_typing certificate.notyping

end CertifiedTermReject

/--
Closed proof-carrying rejection result.

This is the rejection-shaped counterpart of `CertifiedBorrowCheck`: a value of
this type records both a finite executable checker failure and a proof that the
closed source term has no declarative typing derivation.
-/
structure CertifiedBorrowReject (fuel : Nat) (term : Term) : Type where
  certificate :
    CertifiedTermReject fuel FiniteEnv.empty StoreTyping.empty Lifetime.root
      term

namespace CertifiedBorrowReject

def ofTermReject {fuel : Nat} {term : Term}
    (certificate :
      CertifiedTermReject fuel FiniteEnv.empty StoreTyping.empty Lifetime.root
        term) : CertifiedBorrowReject fuel term :=
  { certificate := certificate }

def found? {fuel : Nat} {term : Term}
    (certificate? : Option (CertifiedBorrowReject fuel term)) : Bool :=
  certificate?.isSome

theorem checkedFailure {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowReject fuel term) :
    borrowCheckFailed? fuel term = true := by
  have hchecked := certificate.certificate.checked
  unfold borrowCheckFailed? borrowCheckVerdict? checkProgram?
  unfold checkTermFails? at hchecked
  cases hcheck :
      checkTerm? fuel FiniteEnv.empty StoreTyping.empty Lifetime.root term with
  | ok result =>
      simp [hcheck] at hchecked
  | error message =>
      cases hunknown : checkerErrorUnknown? message
      · simp [hunknown]
      · simp [hcheck, hunknown] at hchecked

theorem borrowReject {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowReject fuel term) :
    LwRust.Paper.borrowReject term :=
  CertifiedTermReject.borrowReject certificate.certificate

theorem checkedFailure_of_found? {fuel : Nat} {term : Term}
    {certificate? : Option (CertifiedBorrowReject fuel term)} :
    found? certificate? = true → borrowCheckFailed? fuel term = true := by
  cases certificate? with
  | none =>
      simp [found?]
  | some certificate =>
      intro _h
      exact certificate.checkedFailure

theorem borrowReject_of_found? {fuel : Nat} {term : Term}
    {certificate? : Option (CertifiedBorrowReject fuel term)} :
    found? certificate? = true → LwRust.Paper.borrowReject term := by
  cases certificate? with
  | none =>
      simp [found?]
  | some certificate =>
      intro _h
      exact certificate.borrowReject

end CertifiedBorrowReject

theorem borrowUnknown?_zero_on_typable_unit :
    borrowUnknown? 0 (.val .unit) = true ∧ borrowCheck (.val .unit) := by
  constructor
  · native_decide
  · exact borrowCheck_of_typing (TermTyping.const ValueTyping.unit)

/--
Fixed-fuel `borrowCheck? = false` is not a sound logical rejection criterion:
fuel exhaustion can make a typable program unknown, and `borrowCheck?` maps
unknown to false.
-/
theorem borrowCheck?_false_not_rejection_complete :
    ¬ (∀ fuel term, borrowCheck? fuel term = false → borrowReject term) := by
  intro hreject
  rcases borrowUnknown?_zero_on_typable_unit with ⟨hunknown, htyped⟩
  exact hreject 0 (.val .unit)
    (borrowCheck?_false_of_borrowUnknown? hunknown) htyped

namespace CheckedTermTypingWitness

theorem borrowCheck {fuel : Nat} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (witness :
      CheckedTermTypingWitness fuel FiniteEnv.empty StoreTyping.empty
        Lifetime.root term expectedTy expectedEnv) :
    LwRust.Paper.borrowCheck term :=
  ⟨expectedTy, expectedEnv.toEnv, witness.typing⟩

end CheckedTermTypingWitness

namespace CertifiedTermCheck

theorem borrowCheck {fuel : Nat} {term : Term} {expectedTy : Ty}
    {expectedEnv : FiniteEnv}
    (certificate :
      CertifiedTermCheck fuel FiniteEnv.empty StoreTyping.empty Lifetime.root
        term expectedTy expectedEnv) :
    LwRust.Paper.borrowCheck term :=
  ⟨expectedTy, expectedEnv.toEnv, certificate.typing⟩

end CertifiedTermCheck

/--
Closed proof-carrying checker result.

This is the certificate-shaped counterpart of `borrowCheck? fuel term`: a value
of this type records the executable successful run and the corresponding
declarative typing derivation from the empty environment.
-/
structure CertifiedBorrowCheck (fuel : Nat) (term : Term) : Type where
  ty : Ty
  env : FiniteEnv
  certificate :
    CertifiedTermCheck fuel FiniteEnv.empty StoreTyping.empty Lifetime.root
      term ty env

namespace CertifiedBorrowCheck

def ofTermCheck {fuel : Nat} {term : Term} {ty : Ty} {env : FiniteEnv}
    (certificate :
      CertifiedTermCheck fuel FiniteEnv.empty StoreTyping.empty Lifetime.root
        term ty env) : CertifiedBorrowCheck fuel term :=
  { ty := ty
    env := env
    certificate := certificate }

def found? {fuel : Nat} {term : Term}
    (certificate? : Option (CertifiedBorrowCheck fuel term)) : Bool :=
  certificate?.isSome

theorem checked {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowCheck fuel term) :
    borrowCheck? fuel term = true := by
  rcases certificate with ⟨ty, env, termCertificate⟩
  have hmatches := termCertificate.checked
  unfold borrowCheck? borrowCheckVerdict? checkProgram?
  unfold checkTermMatches? at hmatches
  cases hcheck :
      checkTerm? fuel FiniteEnv.empty StoreTyping.empty Lifetime.root term with
  | error message =>
      simp [hcheck] at hmatches
  | ok result =>
      simp

theorem borrowCheck {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowCheck fuel term) :
    LwRust.Paper.borrowCheck term :=
  ⟨certificate.ty, certificate.env.toEnv, certificate.certificate.typing⟩

theorem borrowCheck_of_found? {fuel : Nat} {term : Term}
    {certificate? : Option (CertifiedBorrowCheck fuel term)} :
    found? certificate? = true → LwRust.Paper.borrowCheck term := by
  cases certificate? with
  | none =>
      simp [found?]
  | some certificate =>
      intro _h
      exact certificate.borrowCheck

theorem checked_of_found? {fuel : Nat} {term : Term}
    {certificate? : Option (CertifiedBorrowCheck fuel term)} :
    found? certificate? = true → borrowCheck? fuel term = true := by
  cases certificate? with
  | none =>
      simp [found?]
  | some certificate =>
      intro _h
      exact certificate.checked

end CertifiedBorrowCheck

theorem borrowCheck_of_checkProgram?_sound {fuel : Nat} {term : Term}
    (sound :
      ∀ result,
        checkProgram? fuel term = .ok result →
          TermTyping Env.empty StoreTyping.empty Lifetime.root term
            result.ty result.env.toEnv) :
    borrowCheck? fuel term = true → borrowCheck term := by
  intro h
  rcases borrowCheck?_ok h with ⟨result, hresult⟩
  exact borrowCheck_of_typing (sound result hresult)
/-! ## Reflection lemmas for checker soundness -/

private theorem valueTy?_sound {typing : StoreTyping} {value : Value} {ty : Ty} :
    valueTy? typing value = some ty → ValueTyping typing value ty := by
  intro h
  cases value with
  | unit =>
      simp [valueTy?] at h
      subst h
      exact ValueTyping.unit
  | int _ =>
      simp [valueTy?] at h
      subst h
      exact ValueTyping.int
  | bool _ =>
      simp [valueTy?] at h
      subst h
      exact ValueTyping.bool
  | ref ref =>
      exact ValueTyping.ref h

private theorem valueTy?_complete {typing : StoreTyping} {value : Value}
    {ty : Ty} :
    ValueTyping typing value ty → valueTy? typing value = some ty := by
  intro h
  cases h with
  | unit => rfl
  | int => rfl
  | bool => rfl
  | ref hlookup => exact hlookup

private theorem copyTy_sound {ty : Ty} :
    copyTy ty = true → CopyTy ty := by
  intro h
  cases ty with
  | unit => exact CopyTy.unit
  | int => exact CopyTy.int
  | bool => exact CopyTy.bool
  | borrow mutable targets =>
      cases mutable <;> simp [copyTy] at h
      exact CopyTy.immBorrow
  | box inner =>
      simp [copyTy] at h

private theorem copyTy_complete {ty : Ty} :
    CopyTy ty → copyTy ty = true := by
  intro h
  cases h <;> rfl

private theorem tyLoanFree_sound : ∀ {ty : Ty},
    tyLoanFree ty = true → TyLoanFree ty
  | .unit, _ => by
      intro mutable targets hcontains
      cases hcontains
  | .int, _ => by
      intro mutable targets hcontains
      cases hcontains
  | .bool, _ => by
      intro mutable targets hcontains
      cases hcontains
  | .borrow borrowMutable borrowTargets, h => by
      intro mutable targets hcontains
      simp [tyLoanFree] at h
      cases hcontains with
      | here =>
          exact h
  | .box inner, h => by
      intro mutable targets hcontains
      simp [tyLoanFree] at h
      cases hcontains with
      | tyBox hinner =>
          exact tyLoanFree_sound h mutable targets hinner

mutual
  private theorem tyEqv_sameShape {left right : Ty} :
      Ty.eqv left right → Ty.sameShape left right := by
    intro h
    cases left <;> cases right <;> simp [Ty.eqv, Ty.sameShape] at h ⊢
    · exact h.1
    · exact tyEqv_sameShape h

  private theorem partialTyEqv_sameShape {left right : PartialTy} :
      PartialTy.eqv left right → PartialTy.sameShape left right := by
    intro h
    cases left <;> cases right <;> simp [PartialTy.eqv,
      PartialTy.sameShape] at h ⊢
    · exact tyEqv_sameShape h
    · exact partialTyEqv_sameShape h
    · exact tyEqv_sameShape h
end

mutual
  private theorem tyJoin?_some_of_sameShape {left right : Ty} :
      Ty.sameShape left right → ∃ join, tyJoin? left right = some join := by
    intro hshape
    cases hjoin : tyJoin? left right with
    | some join =>
        exact ⟨join, rfl⟩
    | none =>
        exfalso
        cases left <;> cases right <;>
          simp [Ty.sameShape, tyJoin?] at hshape hjoin
        all_goals try contradiction
        rcases tyJoin?_some_of_sameShape hshape with ⟨join, hsome⟩
        exact hjoin join hsome

  private theorem partialTyJoin?_some_of_sameShape {left right : PartialTy} :
      PartialTy.sameShape left right →
        ∃ join, partialTyJoin? left right = some join := by
    intro hshape
    cases hjoin : partialTyJoin? left right with
    | some join =>
        exact ⟨join, rfl⟩
    | none =>
        exfalso
        cases left <;> cases right <;>
          simp [PartialTy.sameShape, partialTyJoin?] at hshape hjoin
        all_goals try contradiction
        · rcases tyJoin?_some_of_sameShape hshape with ⟨join, hsome⟩
          exact hjoin join hsome
        · rcases partialTyJoin?_some_of_sameShape hshape with
            ⟨join, hsome⟩
          exact hjoin join hsome
        · rcases tyJoin?_some_of_sameShape hshape with ⟨join, hsome⟩
          exact hjoin join hsome
end

private theorem lifetimeIntersection?_sound {left right intersection : Lifetime} :
    lifetimeIntersection? left right = some intersection →
      LifetimeIntersection left right intersection := by
  intro h
  unfold lifetimeIntersection? at h
  by_cases hleft : left.contains right
  · simp [hleft] at h
    subst h
    exact LifetimeIntersection.left (by simpa [LifetimeOutlives] using hleft)
  · by_cases hright : right.contains left
    · simp [hleft, hright] at h
      subst h
      exact LifetimeIntersection.right (by simpa [LifetimeOutlives] using hright)
    · simp [hleft, hright] at h

private theorem lifetimeIntersection?_some_of_intersection
    {left right intersection : Lifetime} :
    LifetimeIntersection left right intersection →
      ∃ computed, lifetimeIntersection? left right = some computed := by
  intro hintersection
  have hleft : left ≤ intersection :=
    LifetimeIntersection.left_le hintersection
  have hright : right ≤ intersection :=
    LifetimeIntersection.right_le hintersection
  rcases LifetimeOutlives.comparable_of_common_inner hleft hright with
    hleftRight | hrightLeft
  · exact ⟨right, by
      unfold lifetimeIntersection?
      simp [LifetimeOutlives] at hleftRight
      simp [hleftRight]⟩
  · by_cases hleftRightBool : left.contains right
    · exact ⟨right, by
        unfold lifetimeIntersection?
        simp [hleftRightBool]⟩
    · exact ⟨left, by
        unfold lifetimeIntersection?
        simp [LifetimeOutlives] at hrightLeft
        simp [hleftRightBool, hrightLeft]⟩

private theorem isLifetimeChild_sound {parent child : Lifetime} :
    isLifetimeChild parent child = true → LifetimeChild parent child := by
  intro h
  unfold isLifetimeChild at h
  generalize hdrop : child.path.drop parent.path.length = suffix at h
  cases suffix with
  | nil =>
      simp at h
  | cons label rest =>
      cases rest with
      | cons _ _ =>
          simp at h
      | nil =>
          simp at h
          refine ⟨label, ?_⟩
          have hprefix : parent.path <+: child.path := h
          have happ :
              parent.path ++ child.path.drop parent.path.length = child.path :=
            (List.prefix_iff_eq_append.mp hprefix)
          rw [hdrop] at happ
          exact happ.symm

private theorem isLifetimeChild_complete {parent child : Lifetime} :
    LifetimeChild parent child → isLifetimeChild parent child = true := by
  intro h
  rcases parent with ⟨parentPath⟩
  rcases child with ⟨childPath⟩
  rcases h with ⟨label, hpath⟩
  change childPath = parentPath ++ [label] at hpath
  subst childPath
  simp [isLifetimeChild]

private theorem partialTyStrengthens_borrow_append {mutable : Bool}
    {leftTargets rightTargets : List LVal}
    {joined : PartialTy}
    (hleft : PartialTyStrengthens (.ty (.borrow mutable leftTargets)) joined)
    (hright : PartialTyStrengthens (.ty (.borrow mutable rightTargets)) joined) :
    PartialTyStrengthens
      (.ty (.borrow mutable (leftTargets ++ rightTargets))) joined := by
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
        ⟨targetTargets, rfl, hsubLeft⟩
      have hsubRight : rightTargets ⊆ targetTargets := by
        cases hright with
        | intoUndef hinner' =>
            exact PartialTyStrengthens.borrow_subset hinner'
      exact PartialTyStrengthens.intoUndef (PartialTyStrengthens.borrow (by
        intro target htarget
        rcases List.mem_append.mp htarget with hmem | hmem
        · exact hsubLeft hmem
        · exact hsubRight hmem))

private theorem partialTyUnion_borrow_mem_iff {mutable : Bool}
    {leftTargets rightTargets unionTargets : List LVal} {target : LVal} :
    PartialTyUnion (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets))
      (.ty (.borrow mutable unionTargets)) →
        (target ∈ unionTargets ↔
          target ∈ leftTargets ∨ target ∈ rightTargets) := by
  intro hunion
  constructor
  · intro htarget
    exact PartialTyUnion.borrow_member hunion htarget
  · intro htarget
    rcases htarget with hleft | hright
    · exact PartialTyStrengthens.borrow_subset
        (PartialTyUnion.left_strengthens hunion) hleft
    · exact PartialTyStrengthens.borrow_subset
        (PartialTyUnion.right_strengthens hunion) hright


mutual
  private theorem lvalType?_sound :
      ∀ {fuel : Nat} {env : FiniteEnv} {lv : LVal}
        {partialTy : PartialTy} {lifetime : Lifetime},
        lvalType? fuel env lv = some (partialTy, lifetime) →
          LValTyping env.toEnv lv partialTy lifetime := by
    intro fuel
    cases fuel with
    | zero =>
        intro env lv partialTy lifetime h
        cases lv <;> simp [lvalType?] at h
    | succ fuel =>
        intro env lv partialTy lifetime h
        cases lv with
        | var name =>
            simp [lvalType?] at h
            cases hlookup : env.lookup name with
            | none =>
                simp [hlookup] at h
            | some slot =>
                simp [hlookup] at h
                rcases h with ⟨rfl, rfl⟩
                exact LValTyping.var (show env.toEnv.slotAt name = some slot from hlookup)
        | deref inner =>
            cases hinner : lvalType? fuel env inner with
            | none =>
                simp [lvalType?, hinner] at h
            | some result =>
                rcases result with ⟨innerTy, innerLifetime⟩
                cases innerTy with
                | ty ty =>
                    cases ty with
                    | borrow mutable targets =>
                        simp [lvalType?, hinner] at h
                        exact LValTyping.borrow
                          (lvalType?_sound hinner)
                          (lvalTargetsType?_sound h)
                    | unit =>
                        simp [lvalType?, hinner] at h
                    | int =>
                        simp [lvalType?, hinner] at h
                    | bool =>
                        simp [lvalType?, hinner] at h
                    | box _ =>
                        simp [lvalType?, hinner] at h
                | box innerPartial =>
                    simp [lvalType?, hinner] at h
                    rcases h with ⟨rfl, rfl⟩
                    exact LValTyping.box
                      (lvalType?_sound
                        (partialTy := .box innerPartial)
                        (lifetime := innerLifetime) hinner)
                | undef _ =>
                    simp [lvalType?, hinner] at h

  private theorem lvalTargetsType?_sound :
      ∀ {fuel : Nat} {env : FiniteEnv} {targets : List LVal}
        {partialTy : PartialTy} {lifetime : Lifetime},
        lvalTargetsType? fuel env targets = some (partialTy, lifetime) →
          LValTargetsTyping env.toEnv targets partialTy lifetime := by
    intro fuel env targets
    cases targets with
    | nil =>
        intro partialTy lifetime h
        simp [lvalTargetsType?] at h
    | cons target rest =>
        cases rest with
        | nil =>
            intro partialTy lifetime h
            cases htarget : lvalType? fuel env target with
            | none =>
                simp [lvalTargetsType?, htarget] at h
            | some result =>
                rcases result with ⟨targetTy, targetLifetime⟩
                cases targetTy with
                | ty ty =>
                    simp [lvalTargetsType?, htarget] at h
                    rcases h with ⟨rfl, rfl⟩
                    exact LValTargetsTyping.singleton
                      (lvalType?_sound
                        (partialTy := .ty ty)
                        (lifetime := targetLifetime) htarget)
                | box _ =>
                    simp [lvalTargetsType?, htarget] at h
                | undef _ =>
                    simp [lvalTargetsType?, htarget] at h
        | cons restHead restTail =>
            intro partialTy lifetime h
            cases htarget : lvalType? fuel env target with
            | none =>
                simp [lvalTargetsType?, htarget] at h
            | some targetResult =>
                rcases targetResult with ⟨targetTy, targetLifetime⟩
                cases targetTy with
                | ty headTy =>
                    cases hrest :
                        lvalTargetsType? fuel env (restHead :: restTail) with
                    | none =>
                        simp [lvalTargetsType?, htarget, hrest] at h
                    | some restResult =>
                        rcases restResult with ⟨restTy, restLifetime⟩
                        have restTyping :
                            LValTargetsTyping env.toEnv (restHead :: restTail)
                              restTy restLifetime :=
                          lvalTargetsType?_sound hrest
                        rcases LValTargetsTyping.output_full restTyping with
                          ⟨restFullTy, hrestFull⟩
                        subst hrestFull
                        cases hjoin : tyJoin? headTy restFullTy with
                        | none =>
                            simp [lvalTargetsType?, htarget, hrest,
                              partialTyJoin?, hjoin] at h
                        | some joinTy =>
                            cases hlifetime :
                                lifetimeIntersection? targetLifetime
                                  restLifetime with
                            | none =>
                                simp [lvalTargetsType?, htarget, hrest,
                                  partialTyJoin?, hjoin, hlifetime] at h
                            | some lifetime' =>
                                simp [lvalTargetsType?, htarget, hrest,
                                  partialTyJoin?, hjoin, hlifetime] at h
                                rcases h with ⟨rfl, rfl⟩
                                exact LValTargetsTyping.cons
                                  (lvalType?_sound htarget)
                                  restTyping
                                  (tyJoin?_sound hjoin)
                                  (lifetimeIntersection?_sound hlifetime)
                | box _ =>
                    simp [lvalTargetsType?, htarget] at h
                | undef _ =>
                    simp [lvalTargetsType?, htarget] at h
end

mutual
  private def TyCoherentWitness : Nat → Env → Ty → Prop
    | _, _, .unit => True
    | _, _, .int => True
    | _, _, .bool => True
    | 0, _, .box _ => False
    | fuel + 1, env, .box inner => TyCoherentWitness fuel env inner
    | 0, _, .borrow _ _ => False
    | fuel + 1, env, .borrow _ targets =>
        ∃ targetTy targetLifetime,
          LValTargetsTyping env targets (.ty targetTy) targetLifetime ∧
            TyCoherentWitness fuel env targetTy

  private def PartialTyCoherentWitness : Nat → Env → PartialTy → Prop
    | fuel, env, .ty ty => TyCoherentWitness fuel env ty
    | 0, _, .box _ => False
    | fuel + 1, env, .box inner =>
        PartialTyCoherentWitness fuel env inner
    | _, _, .undef _ => True
end

mutual
  private def TyCoherentNonemptyWitness : Nat → Env → Ty → Prop
    | _, _, .unit => True
    | _, _, .int => True
    | _, _, .bool => True
    | 0, _, .box _ => False
    | fuel + 1, env, .box inner => TyCoherentNonemptyWitness fuel env inner
    | 0, _, .borrow _ targets => targets = []
    | fuel + 1, env, .borrow _ targets =>
        targets = [] ∨
          ∃ targetTy targetLifetime,
            LValTargetsTyping env targets (.ty targetTy) targetLifetime ∧
              TyCoherentNonemptyWitness fuel env targetTy

  private def PartialTyCoherentNonemptyWitness : Nat → Env → PartialTy → Prop
    | fuel, env, .ty ty => TyCoherentNonemptyWitness fuel env ty
    | 0, _, .box _ => False
    | fuel + 1, env, .box inner =>
        PartialTyCoherentNonemptyWitness fuel env inner
    | _, _, .undef _ => True
end

private theorem coherentWitness_sound (fuel : Nat) :
    (∀ {env : FiniteEnv} {ty : Ty},
      tyCoherent fuel env ty = true →
        TyCoherentWitness fuel env.toEnv ty) ∧
    (∀ {env : FiniteEnv} {partialTy : PartialTy},
      partialTyCoherent fuel env partialTy = true →
        PartialTyCoherentWitness fuel env.toEnv partialTy) := by
  induction fuel with
  | zero =>
      have hty :
          ∀ {env : FiniteEnv} {ty : Ty},
            tyCoherent 0 env ty = true →
              TyCoherentWitness 0 env.toEnv ty := by
        intro env ty h
        cases ty <;> simp [tyCoherent, TyCoherentWitness] at h ⊢
      constructor
      · exact hty
      · intro env partialTy h
        cases partialTy with
        | ty ty =>
            exact hty h
        | box inner =>
            simp [partialTyCoherent] at h
        | undef ty =>
            trivial
  | succ fuel ih =>
      have hty :
          ∀ {env : FiniteEnv} {ty : Ty},
            tyCoherent (fuel + 1) env ty = true →
              TyCoherentWitness (fuel + 1) env.toEnv ty := by
        intro env ty h
        cases ty with
        | unit =>
            trivial
        | int =>
            trivial
        | bool =>
            trivial
        | box inner =>
            exact ih.1 (by simpa [tyCoherent] using h)
        | borrow mutable targets =>
            cases htargets : lvalTargetsType? fuel env targets with
            | none =>
                simp [tyCoherent, htargets] at h
            | some result =>
                rcases result with ⟨partialTy, targetLifetime⟩
                cases partialTy with
                | ty targetTy =>
                    have htargetCoherent :
                        tyCoherent fuel env targetTy = true := by
                      simpa [tyCoherent, htargets] using h
                    exact ⟨targetTy, targetLifetime,
                      lvalTargetsType?_sound htargets,
                      ih.1 htargetCoherent⟩
                | box _ =>
                    simp [tyCoherent, htargets] at h
                | undef _ =>
                    simp [tyCoherent, htargets] at h
      constructor
      · exact hty
      · intro env partialTy h
        cases partialTy with
        | ty ty =>
            exact hty h
        | box inner =>
            exact ih.2 (by simpa [partialTyCoherent] using h)
        | undef ty =>
            trivial

private theorem coherentNonemptyWitness_sound (fuel : Nat) :
    (∀ {env : FiniteEnv} {ty : Ty},
      tyCoherentNonempty fuel env ty = true →
        TyCoherentNonemptyWitness fuel env.toEnv ty) ∧
    (∀ {env : FiniteEnv} {partialTy : PartialTy},
      partialTyCoherentNonempty fuel env partialTy = true →
        PartialTyCoherentNonemptyWitness fuel env.toEnv partialTy) := by
  induction fuel with
  | zero =>
      have hty :
          ∀ {env : FiniteEnv} {ty : Ty},
            tyCoherentNonempty 0 env ty = true →
              TyCoherentNonemptyWitness 0 env.toEnv ty := by
        intro env ty h
        cases ty with
        | unit => trivial
        | int => trivial
        | bool => trivial
        | box inner =>
            simp [tyCoherentNonempty, TyCoherentNonemptyWitness] at h
        | borrow mutable targets =>
            simpa [tyCoherentNonempty, TyCoherentNonemptyWitness] using h
      constructor
      · exact hty
      · intro env partialTy h
        cases partialTy with
        | ty ty =>
            exact hty h
        | box inner =>
            simp [partialTyCoherentNonempty,
              PartialTyCoherentNonemptyWitness] at h
        | undef ty =>
            trivial
  | succ fuel ih =>
      have hty :
          ∀ {env : FiniteEnv} {ty : Ty},
            tyCoherentNonempty (fuel + 1) env ty = true →
              TyCoherentNonemptyWitness (fuel + 1) env.toEnv ty := by
        intro env ty h
        cases ty with
        | unit => trivial
        | int => trivial
        | bool => trivial
        | box inner =>
            exact ih.1 (by simpa [tyCoherentNonempty] using h)
        | borrow mutable targets =>
            by_cases htargets : targets = []
            · exact Or.inl htargets
            · cases htargetType : lvalTargetsType? fuel env targets with
              | none =>
                  simp [tyCoherentNonempty, htargets, htargetType] at h
              | some result =>
                  rcases result with ⟨partialTy, targetLifetime⟩
                  cases partialTy with
                  | ty targetTy =>
                      have htargetCoherent :
                          tyCoherentNonempty fuel env targetTy = true := by
                        simpa [tyCoherentNonempty, htargets, htargetType] using h
                      exact Or.inr ⟨targetTy, targetLifetime,
                        lvalTargetsType?_sound htargetType,
                        ih.1 htargetCoherent⟩
                  | box _ =>
                      simp [tyCoherentNonempty, htargets, htargetType] at h
                  | undef _ =>
                      simp [tyCoherentNonempty, htargets, htargetType] at h
      constructor
      · exact hty
      · intro env partialTy h
        cases partialTy with
        | ty ty =>
            exact hty h
        | box inner =>
            exact ih.2 (by simpa [partialTyCoherentNonempty] using h)
        | undef ty =>
            trivial

private def CoherentWitness (fuel : Nat) (env : Env) : Prop :=
  ∀ {name : Name} {slot : EnvSlot},
    env.slotAt name = some slot →
      PartialTyCoherentWitness fuel env slot.ty

private theorem tyCoherent_borrow_targets_sound {fuel : Nat}
    {env : FiniteEnv} {mutable : Bool} {targets : List LVal} :
    tyCoherent fuel env (.borrow mutable targets) = true →
      ∃ targetTy targetLifetime,
        LValTargetsTyping env.toEnv targets (.ty targetTy) targetLifetime := by
  intro h
  cases fuel with
  | zero =>
      simp [tyCoherent] at h
  | succ fuel =>
      cases htargets : lvalTargetsType? fuel env targets with
      | none =>
          simp [tyCoherent, htargets] at h
      | some result =>
          rcases result with ⟨partialTy, targetLifetime⟩
          cases partialTy with
          | ty targetTy =>
              exact ⟨targetTy, targetLifetime, lvalTargetsType?_sound htargets⟩
          | box _ =>
              simp [tyCoherent, htargets] at h
          | undef _ =>
              simp [tyCoherent, htargets] at h

private theorem partialTyCoherent_contains_borrow_targets_sound
    {fuel : Nat} {env : FiniteEnv} {partialTy : PartialTy}
    {needle : Ty} :
    partialTyCoherent fuel env partialTy = true →
      PartialTyContains partialTy needle →
        ∀ {mutable : Bool} {targets : List LVal},
          needle = .borrow mutable targets →
            ∃ targetTy targetLifetime,
              LValTargetsTyping env.toEnv targets (.ty targetTy)
                targetLifetime := by
  intro hcoherent hcontains
  induction hcontains generalizing fuel with
  | here =>
      intro mutable targets hneedle
      cases hneedle
      exact tyCoherent_borrow_targets_sound
        (by simpa [partialTyCoherent] using hcoherent)
  | tyBox _hinner ih =>
      intro mutable targets hneedle
      cases fuel with
      | zero =>
          simp [partialTyCoherent, tyCoherent] at hcoherent
      | succ fuel =>
        exact ih (fuel := fuel)
          (by simpa [partialTyCoherent, tyCoherent] using hcoherent)
          hneedle
  | box _hinner ih =>
      intro mutable targets hneedle
      cases fuel with
      | zero =>
          simp [partialTyCoherent] at hcoherent
      | succ fuel =>
        exact ih (fuel := fuel)
          (by simpa [partialTyCoherent] using hcoherent)
          hneedle

private theorem targetsAllHaveTy?_sound {fuel : Nat} {env : FiniteEnv}
    {ty : Ty} {targets : List LVal} :
    targetsAllHaveTy? fuel env ty targets = true →
      ∀ target, target ∈ targets →
        ∃ lifetime, LValTyping env.toEnv target (.ty ty) lifetime := by
  induction targets with
  | nil =>
      intro _ target htarget
      cases htarget
  | cons head rest ih =>
      intro h target htarget
      cases hhead : lvalType? fuel env head with
      | none =>
          simp [targetsAllHaveTy?, hhead] at h
      | some result =>
          rcases result with ⟨headPartialTy, headLifetime⟩
          cases headPartialTy with
          | ty headTy =>
              by_cases hty : headTy = ty
              · subst headTy
                have hrest : targetsAllHaveTy? fuel env ty rest = true := by
                  simpa [targetsAllHaveTy?, hhead] using h
                cases htarget with
                | head =>
                    exact ⟨headLifetime, lvalType?_sound hhead⟩
                | tail _ htail =>
                    exact ih hrest target htail
              · simp [targetsAllHaveTy?, hhead, hty] at h
          | box _ =>
              simp [targetsAllHaveTy?, hhead] at h
          | undef _ =>
              simp [targetsAllHaveTy?, hhead] at h

private theorem targetListCommonTy?_none_sound {fuel : Nat} {env : FiniteEnv}
    {targets : List LVal} :
    targetListCommonTy? fuel env targets = some none → targets = [] := by
  cases targets with
  | nil =>
      intro _h
      rfl
  | cons head rest =>
      intro h
      cases hhead : lvalType? fuel env head with
      | none =>
          simp [targetListCommonTy?, hhead] at h
      | some result =>
          rcases result with ⟨headPartialTy, headLifetime⟩
          cases headPartialTy with
          | ty ty =>
              cases hall : targetsAllHaveTy? fuel env ty rest <;>
                simp [targetListCommonTy?, hhead, hall] at h
          | box _ =>
              simp [targetListCommonTy?, hhead] at h
          | undef _ =>
              simp [targetListCommonTy?, hhead] at h

private theorem targetListCommonTy?_some_sound {fuel : Nat} {env : FiniteEnv}
    {targets : List LVal} {ty : Ty} :
    targetListCommonTy? fuel env targets = some (some ty) →
      ∀ target, target ∈ targets →
        ∃ lifetime, LValTyping env.toEnv target (.ty ty) lifetime := by
  cases targets with
  | nil =>
      intro h
      simp [targetListCommonTy?] at h
  | cons head rest =>
      intro h target htarget
      cases hhead : lvalType? fuel env head with
      | none =>
          simp [targetListCommonTy?, hhead] at h
      | some result =>
          rcases result with ⟨headPartialTy, headLifetime⟩
          cases headPartialTy with
          | ty headTy =>
              cases hall : targetsAllHaveTy? fuel env headTy rest
              · simp [targetListCommonTy?, hhead, hall] at h
              · simp [targetListCommonTy?, hhead, hall] at h
                subst h
                cases htarget with
                | head =>
                    exact ⟨headLifetime, lvalType?_sound hhead⟩
                | tail _ htail =>
                    exact targetsAllHaveTy?_sound hall target htail
          | box _ =>
              simp [targetListCommonTy?, hhead] at h
          | undef _ =>
              simp [targetListCommonTy?, hhead] at h

private theorem shapeCompatible_sound (fuel : Nat) :
    (∀ {env : FiniteEnv} {left right : Ty},
      shapeCompatibleTy fuel env left right = true →
        ShapeCompatible env.toEnv (.ty left) (.ty right)) ∧
    (∀ {env : FiniteEnv} {left right : PartialTy},
      shapeCompatiblePartialTy fuel env left right = true →
        ShapeCompatible env.toEnv left right) := by
  induction fuel with
  | zero =>
      constructor
      · intro env left right h
        simp [shapeCompatibleTy] at h
      · intro env left right h
        simp [shapeCompatiblePartialTy] at h
  | succ fuel ih =>
      constructor
      · intro env left right h
        cases left with
        | unit =>
            cases right <;> simp [shapeCompatibleTy] at h
            exact ShapeCompatible.unit
        | int =>
            cases right <;> simp [shapeCompatibleTy] at h
            exact ShapeCompatible.int
        | bool =>
            cases right <;> simp [shapeCompatibleTy] at h
            exact ShapeCompatible.bool
        | box left =>
            cases right <;> simp [shapeCompatibleTy] at h
            next right =>
              exact ShapeCompatible.tyBox (ih.1 h)
        | borrow mutable₁ leftTargets =>
            cases right <;> simp [shapeCompatibleTy] at h
            next mutable₂ rightTargets =>
              by_cases hmutable : mutable₁ = mutable₂
              · subst mutable₂
                simp at h
                cases hleft :
                    targetListCommonTy? fuel env leftTargets with
                | none =>
                    simp [hleft] at h
                | some leftCommon =>
                    cases hright :
                        targetListCommonTy? fuel env rightTargets with
                    | none =>
                        simp [hleft, hright] at h
                    | some rightCommon =>
                        cases leftCommon with
                        | none =>
                            have hleftEmpty :
                                leftTargets = [] :=
                              targetListCommonTy?_none_sound hleft
                            cases rightCommon with
                            | none =>
                                have hrightEmpty :
                                    rightTargets = [] :=
                                  targetListCommonTy?_none_sound hright
                                subst leftTargets
                                subst rightTargets
                                refine ShapeCompatible.borrow ?_ ?_
                                  ShapeCompatible.unit
                                · intro target htarget
                                  cases htarget
                                · intro target htarget
                                  cases htarget
                            | some rightTy =>
                                simp [hleft, hright] at h
                                subst leftTargets
                                refine ShapeCompatible.borrow ?_ ?_ (ih.1 h)
                                · intro target htarget
                                  cases htarget
                                · exact targetListCommonTy?_some_sound hright
                        | some leftTy =>
                            cases rightCommon with
                            | none =>
                                simp [hleft, hright] at h
                                have hrightEmpty :
                                    rightTargets = [] :=
                                  targetListCommonTy?_none_sound hright
                                subst rightTargets
                                refine ShapeCompatible.borrow ?_ ?_ (ih.1 h)
                                · exact targetListCommonTy?_some_sound hleft
                                · intro target htarget
                                  cases htarget
                            | some rightTy =>
                                simp [hleft, hright] at h
                                refine ShapeCompatible.borrow ?_ ?_ (ih.1 h)
                                · exact targetListCommonTy?_some_sound hleft
                                · exact targetListCommonTy?_some_sound hright
              · simp [hmutable] at h
      · intro env left right h
        cases left with
        | ty leftTy =>
            cases right <;> simp [shapeCompatiblePartialTy] at h
            · exact ih.1 h
            · exact ShapeCompatible.undefRight (ih.2 h)
        | box leftInner =>
            cases right <;> simp [shapeCompatiblePartialTy] at h
            · exact ShapeCompatible.box (ih.2 h)
            · exact ShapeCompatible.undefRight (ih.2 h)
        | undef leftTy =>
            simp [shapeCompatiblePartialTy] at h
            exact ShapeCompatible.undefLeft (ih.2 h)

private theorem shapeCompatibleTy_sound {fuel : Nat} {env : FiniteEnv}
    {left right : Ty} :
    shapeCompatibleTy fuel env left right = true →
      ShapeCompatible env.toEnv (.ty left) (.ty right) :=
  (shapeCompatible_sound fuel).1

private theorem shapeCompatiblePartialTy_sound {fuel : Nat} {env : FiniteEnv}
    {left right : PartialTy} :
    shapeCompatiblePartialTy fuel env left right = true →
      ShapeCompatible env.toEnv left right :=
  (shapeCompatible_sound fuel).2

private theorem lifetimeOutlives_sound {outer inner : Lifetime} :
    lifetimeOutlives outer inner = true → LifetimeOutlives outer inner := by
  intro h
  simpa [lifetimeOutlives, LifetimeOutlives] using h

private theorem lvalBaseOutlives_sound {env : FiniteEnv} {lv : LVal}
    {lifetime : Lifetime} :
    lvalBaseOutlives env lv lifetime = true →
      LValBaseOutlives env.toEnv lv lifetime := by
  intro h
  unfold lvalBaseOutlives at h
  cases hlookup : env.lookup (LVal.base lv) with
  | none =>
      simp [hlookup] at h
  | some slot =>
      exact ⟨slot, hlookup, lifetimeOutlives_sound (by
        simpa [hlookup] using h)⟩

private theorem borrowTargetsWellFormed_sound {fuel : Nat} {env : FiniteEnv}
    {targets : List LVal} {lifetime : Lifetime} :
    borrowTargetsWellFormed fuel env targets lifetime = true →
      BorrowTargetsWellFormed env.toEnv targets lifetime := by
  intro h
  refine BorrowTargetsWellFormed.intro ?_
  intro target htarget
  unfold borrowTargetsWellFormed at h
  have htargetCheck := (List.all_eq_true.mp h) target htarget
  cases htype : lvalType? fuel env target with
  | none =>
      simp [htype] at htargetCheck
  | some result =>
      rcases result with ⟨partialTy, targetLifetime⟩
      cases partialTy with
      | ty targetTy =>
          simp [htype] at htargetCheck
          exact ⟨targetTy, targetLifetime, lvalType?_sound htype,
            lifetimeOutlives_sound htargetCheck.1,
            lvalBaseOutlives_sound htargetCheck.2⟩
      | box _ =>
          simp [htype] at htargetCheck
      | undef _ =>
          simp [htype] at htargetCheck

private theorem wellFormedTy_sound :
    ∀ {fuel : Nat} {env : FiniteEnv} {ty : Ty} {lifetime : Lifetime},
      wellFormedTy fuel env ty lifetime = true →
        WellFormedTy env.toEnv ty lifetime
  | _fuel, _env, .unit, _lifetime, _h => WellFormedTy.unit
  | _fuel, _env, .int, _lifetime, _h => WellFormedTy.int
  | _fuel, _env, .bool, _lifetime, _h => WellFormedTy.bool
  | _fuel, _env, .borrow _ _, _lifetime, h =>
      WellFormedTy.borrow (borrowTargetsWellFormed_sound h)
  | _fuel, _env, .box _, _lifetime, h =>
      WellFormedTy.box (wellFormedTy_sound h)

private theorem strike?_sound {path : Path} {source struck : PartialTy} :
    strike? path source = some struck → Strike path source struck := by
  intro h
  induction path generalizing source struck with
  | nil =>
      cases source <;> simp [strike?] at h
      next ty =>
        cases h
        rfl
  | cons _ rest ih =>
      cases source <;> simp [strike?] at h
      next inner =>
        cases hinner : strike? rest inner with
        | none =>
            simp [hinner] at h
        | some innerStruck =>
            simp [hinner] at h
            cases h
            exact ih hinner

private theorem envMove?_sound {env moved : FiniteEnv} {lv : LVal} :
    envMove? env lv = some moved → EnvMove env.toEnv lv moved.toEnv := by
  intro h
  unfold envMove? at h
  cases hslot : env.lookup (LVal.base lv) with
  | none =>
      simp [hslot] at h
  | some slot =>
      cases hstrike : strike? (LVal.path lv) slot.ty with
      | none =>
          simp [hslot, hstrike] at h
      | some struck =>
          simp [hslot, hstrike] at h
          cases h
          refine ⟨slot, struck, hslot, strike?_sound hstrike, ?_⟩
          simp [FiniteEnv.toEnv_update]

private theorem termDiverges_sound {term : Term} :
    termDiverges term = true → Term.Diverges term := by
  exact
    Term.rec
      (motive_1 := fun term => termDiverges term = true → Term.Diverges term)
      (motive_2 := fun terms =>
        termListDiverges terms = true →
          ∃ term, term ∈ terms ∧ Term.Diverges term)
      (by
        intro lifetime terms ih h
        simp [termDiverges] at h
        rcases ih h with ⟨term, hmem, hdiv⟩
        exact Term.Diverges.block hmem hdiv)
      (by intro _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ h; unfold termDiverges at h; simp at h)
      (by intro _ h; unfold termDiverges at h; simp at h)
      (by intro _ h; unfold termDiverges at h; simp at h)
      (by intro _; exact Term.Diverges.missing)
      (by intro _ _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ _ _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ _ _ _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro _ _ _ _ _ _ _ h; unfold termDiverges at h; simp at h)
      (by intro h; simp [termListDiverges] at h)
      (by
        intro head tail ihHead ihTail h
        simp [termListDiverges] at h
        rcases h with h | h
        · exact ⟨head, by simp, ihHead h⟩
        · rcases ihTail h with ⟨term, hmem, hdiv⟩
          exact ⟨term, List.mem_cons_of_mem _ hmem, hdiv⟩)
      term

private theorem lookupEntries_mem {entries : List (Name × EnvSlot)}
    {name : Name} {slot : EnvSlot} :
    FiniteEnv.lookupEntries entries name = some slot →
      (name, slot) ∈ entries := by
  induction entries with
  | nil =>
      intro h
      simp [FiniteEnv.lookupEntries] at h
  | cons entry rest ih =>
      intro h
      rcases entry with ⟨entryName, entrySlot⟩
      by_cases hname : name = entryName
      · subst hname
        simp [FiniteEnv.lookupEntries] at h
        cases h
        exact List.mem_cons_self
      · simp [FiniteEnv.lookupEntries, hname] at h
        exact List.mem_cons_of_mem _ (ih h)

private theorem coherent_witness_sound {fuel : Nat} {env : FiniteEnv} :
    coherent fuel env = true →
      CoherentWitness fuel env.toEnv := by
  intro hcoherent name slot hslot
  have hentry : (name, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  unfold coherent at hcoherent
  have hentryCheck :=
    (List.all_eq_true.mp hcoherent) (name, slot) hentry
  exact (coherentWitness_sound fuel).2 hentryCheck

private theorem rootCoherent_witness_sound {fuel : Nat} {env : FiniteEnv}
    {root : Name} :
    rootCoherent fuel env root = true →
    ∀ {slot : EnvSlot},
      env.lookup root = some slot →
        PartialTyCoherentWitness fuel env.toEnv slot.ty := by
  intro hroot slot hslot
  have hslotCoherent : partialTyCoherent fuel env slot.ty = true := by
    simpa [rootCoherent, hslot] using hroot
  exact (coherentWitness_sound fuel).2 hslotCoherent

private theorem tyCoherentNonempty_borrow_targets_sound {fuel : Nat}
    {env : FiniteEnv} {mutable : Bool} {targets : List LVal} :
    tyCoherentNonempty fuel env (.borrow mutable targets) = true →
    targets ≠ [] →
      ∃ targetTy targetLifetime,
        LValTargetsTyping env.toEnv targets (.ty targetTy) targetLifetime := by
  intro h hnonempty
  cases fuel with
  | zero =>
      simp [tyCoherentNonempty] at h
      exact False.elim (hnonempty h)
  | succ fuel =>
      by_cases htargets : targets = []
      · exact False.elim (hnonempty htargets)
      · cases htargetType : lvalTargetsType? fuel env targets with
        | none =>
            simp [tyCoherentNonempty, htargets, htargetType] at h
        | some result =>
            rcases result with ⟨partialTy, targetLifetime⟩
            cases partialTy with
            | ty targetTy =>
                exact ⟨targetTy, targetLifetime,
                  lvalTargetsType?_sound htargetType⟩
            | box _ =>
                simp [tyCoherentNonempty, htargets, htargetType] at h
            | undef _ =>
                simp [tyCoherentNonempty, htargets, htargetType] at h

private theorem partialTyCoherentNonempty_contains_borrow_targets_sound_aux
    {fuel : Nat} {env : FiniteEnv} {partialTy : PartialTy}
    {needle : Ty} :
    partialTyCoherentNonempty fuel env partialTy = true →
    PartialTyContains partialTy needle →
      ∀ {mutable : Bool} {targets : List LVal},
        needle = .borrow mutable targets →
        targets ≠ [] →
          ∃ targetTy targetLifetime,
            LValTargetsTyping env.toEnv targets (.ty targetTy)
              targetLifetime := by
  intro hcoherent hcontains
  induction hcontains generalizing fuel with
  | here =>
      intro mutable targets hneedle hnonempty
      cases hneedle
      exact tyCoherentNonempty_borrow_targets_sound
        (by simpa [partialTyCoherentNonempty] using hcoherent)
        hnonempty
  | tyBox _hinner ih =>
      intro mutable targets hneedle hnonempty
      cases fuel with
      | zero =>
          simp [partialTyCoherentNonempty, tyCoherentNonempty] at hcoherent
      | succ fuel =>
          exact ih (fuel := fuel)
            (by simpa [partialTyCoherentNonempty, tyCoherentNonempty] using
              hcoherent)
            hneedle hnonempty
  | box _hinner ih =>
      intro mutable targets hneedle hnonempty
      cases fuel with
      | zero =>
          simp [partialTyCoherentNonempty] at hcoherent
      | succ fuel =>
          exact ih (fuel := fuel)
            (by simpa [partialTyCoherentNonempty] using hcoherent)
            hneedle hnonempty

private theorem partialTyCoherentNonempty_contains_borrow_targets_sound
    {fuel : Nat} {env : FiniteEnv} {partialTy : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    partialTyCoherentNonempty fuel env partialTy = true →
    PartialTyContains partialTy (.borrow mutable targets) →
    targets ≠ [] →
      ∃ targetTy targetLifetime,
        LValTargetsTyping env.toEnv targets (.ty targetTy) targetLifetime := by
  intro hcoherent hcontains hnonempty
  exact partialTyCoherentNonempty_contains_borrow_targets_sound_aux
    hcoherent hcontains rfl hnonempty

private theorem coherentNonempty_slot_contains_borrow_targets_sound
    {fuel : Nat} {env : FiniteEnv} {name : Name} {slot : EnvSlot}
    {mutable : Bool} {targets : List LVal} :
    coherentNonempty fuel env = true →
    env.lookup name = some slot →
    PartialTyContains slot.ty (.borrow mutable targets) →
    targets ≠ [] →
      ∃ targetTy targetLifetime,
        LValTargetsTyping env.toEnv targets (.ty targetTy) targetLifetime := by
  intro hcoherent hslot hcontains hnonempty
  have hentry : (name, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  unfold coherentNonempty at hcoherent
  have hentryCheck :=
    (List.all_eq_true.mp hcoherent) (name, slot) hentry
  exact partialTyCoherentNonempty_contains_borrow_targets_sound
    hentryCheck hcontains hnonempty

private theorem partialTyCoherentWitness_contains_borrow_targets_aux
    {fuel : Nat} {env : Env} {partialTy : PartialTy} {needle : Ty} :
    PartialTyCoherentWitness fuel env partialTy →
      PartialTyContains partialTy needle →
        ∀ {mutable : Bool} {targets : List LVal},
          needle = .borrow mutable targets →
            ∃ targetTy targetLifetime,
              LValTargetsTyping env targets (.ty targetTy) targetLifetime := by
  intro hwitness hcontains
  induction hcontains generalizing fuel with
  | here =>
      intro mutable targets hneedle
      cases hneedle
      cases fuel with
      | zero =>
          exact False.elim hwitness
      | succ fuel =>
          rcases hwitness with ⟨targetTy, targetLifetime, htargets, _⟩
          exact ⟨targetTy, targetLifetime, htargets⟩
  | tyBox _hinner ih =>
      intro mutable targets hneedle
      cases fuel with
      | zero =>
          exact False.elim hwitness
      | succ fuel =>
          exact ih (fuel := fuel)
            (by simpa [PartialTyCoherentWitness, TyCoherentWitness] using
              hwitness)
            hneedle
  | box _hinner ih =>
      intro mutable targets hneedle
      cases fuel with
      | zero =>
          exact False.elim hwitness
      | succ fuel =>
          exact ih (fuel := fuel)
            (by simpa [PartialTyCoherentWitness] using hwitness)
            hneedle

private theorem partialTyCoherentWitness_contains_borrow_targets
    {fuel : Nat} {env : Env} {partialTy : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    PartialTyCoherentWitness fuel env partialTy →
      PartialTyContains partialTy (.borrow mutable targets) →
        ∃ targetTy targetLifetime,
          LValTargetsTyping env targets (.ty targetTy) targetLifetime := by
  intro hwitness hcontains
  exact partialTyCoherentWitness_contains_borrow_targets_aux
    hwitness hcontains rfl

private theorem partialTyCoherentWitness_borrow_targets_nonempty
    {fuel : Nat} {env : Env} {partialTy : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    PartialTyCoherentWitness fuel env partialTy →
      PartialTyContains partialTy (.borrow mutable targets) →
        targets ≠ [] := by
  intro hwitness hcontains hnil
  rcases partialTyCoherentWitness_contains_borrow_targets
      hwitness hcontains with
    ⟨targetTy, targetLifetime, htargets⟩
  subst hnil
  exact LValTargetsTyping.nil_false htargets

private theorem tyCoherentWitness_of_eqv (fuel : Nat) {env : Env}
    (hlinear : Linearizable env) :
    (∀ {left right : Ty},
      Ty.eqv left right →
      TyCoherentWitness fuel env left →
        TyCoherentWitness fuel env right) ∧
    (∀ {left right : PartialTy},
      PartialTy.eqv left right →
      PartialTyCoherentWitness fuel env left →
        PartialTyCoherentWitness fuel env right) := by
  induction fuel with
  | zero =>
      have hty :
          ∀ {left right : Ty},
            Ty.eqv left right →
            TyCoherentWitness 0 env left →
              TyCoherentWitness 0 env right := by
        intro left right heqv hwitness
        cases left <;> cases right <;>
          simp [Ty.eqv, TyCoherentWitness] at heqv hwitness ⊢
      have hpartial :
          ∀ {left right : PartialTy},
            PartialTy.eqv left right →
            PartialTyCoherentWitness 0 env left →
              PartialTyCoherentWitness 0 env right := by
        intro left right heqv hwitness
        cases left with
        | ty leftTy =>
            cases right with
            | ty rightTy =>
                exact hty heqv hwitness
            | box _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | box leftInner =>
            cases right <;>
              simp [PartialTy.eqv, PartialTyCoherentWitness] at heqv hwitness ⊢
        | undef leftTy =>
            cases right <;>
              simp [PartialTy.eqv, PartialTyCoherentWitness] at heqv hwitness ⊢
      constructor
      · exact hty
      · exact hpartial
  | succ fuel ih =>
      have hty :
          ∀ {left right : Ty},
            Ty.eqv left right →
            TyCoherentWitness (fuel + 1) env left →
              TyCoherentWitness (fuel + 1) env right := by
        intro left right heqv hwitness
        cases left with
        | unit =>
            cases right <;>
              simp [Ty.eqv, TyCoherentWitness] at heqv hwitness ⊢
        | int =>
            cases right <;>
              simp [Ty.eqv, TyCoherentWitness] at heqv hwitness ⊢
        | bool =>
            cases right <;>
              simp [Ty.eqv, TyCoherentWitness] at heqv hwitness ⊢
        | box leftInner =>
            cases right with
            | box rightInner =>
                change TyCoherentWitness fuel env leftInner at hwitness
                change TyCoherentWitness fuel env rightInner
                exact ih.1 (by simpa [Ty.eqv] using heqv) hwitness
            | unit =>
                simp [Ty.eqv] at heqv
            | int =>
                simp [Ty.eqv] at heqv
            | borrow _ _ =>
                simp [Ty.eqv] at heqv
            | bool =>
                simp [Ty.eqv] at heqv
        | borrow leftMutable leftTargets =>
            cases right with
            | borrow rightMutable rightTargets =>
                simp [Ty.eqv] at heqv
                change ∃ targetTy targetLifetime,
                  LValTargetsTyping env leftTargets (.ty targetTy)
                    targetLifetime ∧
                    TyCoherentWitness fuel env targetTy at hwitness
                change ∃ targetTy targetLifetime,
                  LValTargetsTyping env rightTargets (.ty targetTy)
                    targetLifetime ∧
                    TyCoherentWitness fuel env targetTy
                rcases heqv with ⟨hmutable, hleftRight, hrightLeft⟩
                subst rightMutable
                rcases hwitness with
                  ⟨targetTy, targetLifetime, htargets, htargetWitness⟩
                have htargetsNonempty : rightTargets ≠ [] := by
                  intro hnil
                  subst hnil
                  cases leftTargets with
                  | nil =>
                      exact LValTargetsTyping.nil_false htargets
                  | cons head tail =>
                      have hmem : head ∈ ([] : List LVal) :=
                        hleftRight (by simp)
                      cases hmem
                rcases lvalTargetsTyping_of_nonempty_subset htargets
                    htargetsNonempty hrightLeft with
                  ⟨rightTargetTy, rightTargetLifetime, hrightTargets,
                    _hrightStrengthens, _hrightLifetime⟩
                rcases hlinear with ⟨φ, hφ⟩
                have heqvTargets :
                    PartialTy.eqv (.ty targetTy) (.ty rightTargetTy) :=
                  lvalTargetsTyping_eqv_of_subset_of_lval_eqv
                    (env := env)
                    (leftTargets := leftTargets) (rightTargets := rightTargets)
                    (leftTy := .ty targetTy)
                    (rightTy := .ty rightTargetTy)
                    (leftLifetime := targetLifetime)
                    (rightLifetime := rightTargetLifetime)
                    (fun hleft hright =>
                      lvalTyping_eqv_of_linearizedBy hφ hleft hright)
                    htargets hrightTargets hleftRight hrightLeft
                exact ⟨rightTargetTy, rightTargetLifetime, hrightTargets,
                  ih.1 heqvTargets htargetWitness⟩
            | unit =>
                simp [Ty.eqv] at heqv
            | int =>
                simp [Ty.eqv] at heqv
            | box _ =>
                simp [Ty.eqv] at heqv
            | bool =>
                simp [Ty.eqv] at heqv
      have hpartial :
          ∀ {left right : PartialTy},
            PartialTy.eqv left right →
            PartialTyCoherentWitness (fuel + 1) env left →
              PartialTyCoherentWitness (fuel + 1) env right := by
        intro left right heqv hwitness
        cases left with
        | ty leftTy =>
            cases right with
            | ty rightTy =>
                exact hty heqv hwitness
            | box _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | box leftInner =>
            cases right with
            | box rightInner =>
                exact ih.2 (by simpa [PartialTy.eqv] using heqv)
                  (by simpa [PartialTyCoherentWitness] using hwitness)
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | undef leftTy =>
            cases right with
            | undef rightTy =>
                trivial
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | box _ =>
                simp [PartialTy.eqv] at heqv
      constructor
      · exact hty
      · exact hpartial

private theorem partialTyCoherentWitness_of_eqv {fuel : Nat} {env : Env}
    (hlinear : Linearizable env) {left right : PartialTy} :
    PartialTy.eqv left right →
    PartialTyCoherentWitness fuel env left →
      PartialTyCoherentWitness fuel env right :=
  (tyCoherentWitness_of_eqv fuel hlinear).2

private theorem tyCoherentNonemptyWitness_of_eqv (fuel : Nat) {env : Env}
    (hlinear : Linearizable env) :
    (∀ {left right : Ty},
      Ty.eqv left right →
      TyCoherentNonemptyWitness fuel env left →
        TyCoherentNonemptyWitness fuel env right) ∧
    (∀ {left right : PartialTy},
      PartialTy.eqv left right →
      PartialTyCoherentNonemptyWitness fuel env left →
        PartialTyCoherentNonemptyWitness fuel env right) := by
  induction fuel with
  | zero =>
      have hty :
          ∀ {left right : Ty},
            Ty.eqv left right →
            TyCoherentNonemptyWitness 0 env left →
              TyCoherentNonemptyWitness 0 env right := by
        intro left right heqv hwitness
        cases left with
        | unit =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | int =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | bool =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | box _ =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | borrow leftMutable leftTargets =>
            cases right with
            | borrow rightMutable rightTargets =>
                simp [Ty.eqv] at heqv
                rcases heqv with ⟨hmutable, _hleftRight, hrightLeft⟩
                subst rightMutable
                cases rightTargets with
                | nil => rfl
                | cons head tail =>
                    have hmem : head ∈ leftTargets :=
                      hrightLeft (by simp)
                    rw [hwitness] at hmem
                    cases hmem
            | unit | int | box _ | bool =>
                simp [Ty.eqv] at heqv
      have hpartial :
          ∀ {left right : PartialTy},
            PartialTy.eqv left right →
            PartialTyCoherentNonemptyWitness 0 env left →
              PartialTyCoherentNonemptyWitness 0 env right := by
        intro left right heqv hwitness
        cases left with
        | ty leftTy =>
            cases right with
            | ty rightTy =>
                exact hty heqv hwitness
            | box _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | box leftInner =>
            cases right <;>
              simp [PartialTy.eqv, PartialTyCoherentNonemptyWitness] at heqv hwitness ⊢
        | undef leftTy =>
            cases right <;>
              simp [PartialTy.eqv, PartialTyCoherentNonemptyWitness] at heqv hwitness ⊢
      constructor
      · exact hty
      · exact hpartial
  | succ fuel ih =>
      have hty :
          ∀ {left right : Ty},
            Ty.eqv left right →
            TyCoherentNonemptyWitness (fuel + 1) env left →
              TyCoherentNonemptyWitness (fuel + 1) env right := by
        intro left right heqv hwitness
        cases left with
        | unit =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | int =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | bool =>
            cases right <;>
              simp [Ty.eqv, TyCoherentNonemptyWitness] at heqv hwitness ⊢
        | box leftInner =>
            cases right with
            | box rightInner =>
                change TyCoherentNonemptyWitness fuel env leftInner at hwitness
                change TyCoherentNonemptyWitness fuel env rightInner
                exact ih.1 (by simpa [Ty.eqv] using heqv) hwitness
            | unit | int | borrow _ _ | bool =>
                simp [Ty.eqv] at heqv
        | borrow leftMutable leftTargets =>
            cases right with
            | borrow rightMutable rightTargets =>
                simp [Ty.eqv] at heqv
                rcases heqv with ⟨hmutable, hleftRight, hrightLeft⟩
                subst rightMutable
                cases hwitness with
                | inl hleftEmpty =>
                    left
                    cases rightTargets with
                    | nil => rfl
                    | cons head tail =>
                        have hmem : head ∈ leftTargets :=
                          hrightLeft (by simp)
                        rw [hleftEmpty] at hmem
                        cases hmem
                | inr hwitnessNonempty =>
                    rcases hwitnessNonempty with
                      ⟨targetTy, targetLifetime, htargets, htargetWitness⟩
                    by_cases hrightEmpty : rightTargets = []
                    · exact Or.inl hrightEmpty
                    · rcases lvalTargetsTyping_of_nonempty_subset htargets
                        hrightEmpty hrightLeft with
                      ⟨rightTargetTy, rightTargetLifetime, hrightTargets,
                        _hrightStrengthens, _hrightLifetime⟩
                      rcases hlinear with ⟨φ, hφ⟩
                      have heqvTargets :
                          PartialTy.eqv (.ty targetTy) (.ty rightTargetTy) :=
                        lvalTargetsTyping_eqv_of_subset_of_lval_eqv
                          (env := env)
                          (leftTargets := leftTargets)
                          (rightTargets := rightTargets)
                          (leftTy := .ty targetTy)
                          (rightTy := .ty rightTargetTy)
                          (leftLifetime := targetLifetime)
                          (rightLifetime := rightTargetLifetime)
                          (fun hleft hright =>
                            lvalTyping_eqv_of_linearizedBy hφ hleft hright)
                          htargets hrightTargets hleftRight hrightLeft
                      exact Or.inr ⟨rightTargetTy, rightTargetLifetime,
                        hrightTargets, ih.1 heqvTargets htargetWitness⟩
            | unit | int | box _ | bool =>
                simp [Ty.eqv] at heqv
      have hpartial :
          ∀ {left right : PartialTy},
            PartialTy.eqv left right →
            PartialTyCoherentNonemptyWitness (fuel + 1) env left →
              PartialTyCoherentNonemptyWitness (fuel + 1) env right := by
        intro left right heqv hwitness
        cases left with
        | ty leftTy =>
            cases right with
            | ty rightTy =>
                exact hty heqv hwitness
            | box _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | box leftInner =>
            cases right with
            | box rightInner =>
                exact ih.2 (by simpa [PartialTy.eqv] using heqv)
                  (by simpa [PartialTyCoherentNonemptyWitness] using hwitness)
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | undef _ =>
                simp [PartialTy.eqv] at heqv
        | undef leftTy =>
            cases right with
            | undef rightTy =>
                trivial
            | ty _ =>
                simp [PartialTy.eqv] at heqv
            | box _ =>
                simp [PartialTy.eqv] at heqv
      constructor
      · exact hty
      · exact hpartial

private theorem partialTyCoherentNonemptyWitness_of_eqv {fuel : Nat}
    {env : Env} (hlinear : Linearizable env) {left right : PartialTy} :
    PartialTy.eqv left right →
    PartialTyCoherentNonemptyWitness fuel env left →
      PartialTyCoherentNonemptyWitness fuel env right :=
  (tyCoherentNonemptyWitness_of_eqv fuel hlinear).2

private theorem partialTyCoherentNonemptyWitness_contains_borrow_targets_aux
    {fuel : Nat} {env : Env} {partialTy : PartialTy} {needle : Ty} :
    PartialTyCoherentNonemptyWitness fuel env partialTy →
      PartialTyContains partialTy needle →
        ∀ {mutable : Bool} {targets : List LVal},
          needle = .borrow mutable targets →
          targets ≠ [] →
            ∃ targetTy targetLifetime,
              LValTargetsTyping env targets (.ty targetTy) targetLifetime := by
  intro hwitness hcontains
  induction hcontains generalizing fuel with
  | here =>
      intro mutable targets hneedle hnonempty
      cases hneedle
      cases fuel with
      | zero =>
          exact False.elim (hnonempty hwitness)
      | succ fuel =>
          cases hwitness with
          | inl hempty =>
              exact False.elim (hnonempty hempty)
          | inr hwitnessNonempty =>
              rcases hwitnessNonempty with
                ⟨targetTy, targetLifetime, htargets, _htargetWitness⟩
              exact ⟨targetTy, targetLifetime, htargets⟩
  | tyBox _hinner ih =>
      intro mutable targets hneedle hnonempty
      cases fuel with
      | zero =>
          exact False.elim hwitness
      | succ fuel =>
          exact ih (fuel := fuel)
            (by simpa [PartialTyCoherentNonemptyWitness,
              TyCoherentNonemptyWitness] using hwitness)
            hneedle hnonempty
  | box _hinner ih =>
      intro mutable targets hneedle hnonempty
      cases fuel with
      | zero =>
          exact False.elim hwitness
      | succ fuel =>
          exact ih (fuel := fuel)
            (by simpa [PartialTyCoherentNonemptyWitness] using hwitness)
            hneedle hnonempty

private theorem partialTyCoherentNonemptyWitness_contains_borrow_targets
    {fuel : Nat} {env : Env} {partialTy : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    PartialTyCoherentNonemptyWitness fuel env partialTy →
      PartialTyContains partialTy (.borrow mutable targets) →
      targets ≠ [] →
        ∃ targetTy targetLifetime,
          LValTargetsTyping env targets (.ty targetTy) targetLifetime := by
  intro hwitness hcontains hnonempty
  exact partialTyCoherentNonemptyWitness_contains_borrow_targets_aux
    hwitness hcontains rfl hnonempty

private theorem coherentWitness_lvalTyping_witness {fuel : Nat}
    {env : Env}
    (hwitness : CoherentWitness fuel env)
    (hlinear : Linearizable env) :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env lv partialTy lifetime →
        ∃ witnessFuel,
          witnessFuel ≤ fuel ∧
            PartialTyCoherentWitness witnessFuel env partialTy := by
  intro lv partialTy lifetime htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy _lifetime _ =>
      ∃ witnessFuel,
        witnessFuel ≤ fuel ∧
          PartialTyCoherentWitness witnessFuel env partialTy)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    ?var ?box ?borrow ?singleton ?cons htyping
  · intro _x _slot hslot
    exact ⟨fuel, Nat.le_refl fuel, hwitness hslot⟩
  · intro _lv inner _lifetime _htyping ih
    rcases ih with ⟨witnessFuel, hwitnessFuelLe, hinnerBox⟩
    cases witnessFuel with
    | zero =>
        exact False.elim hinnerBox
    | succ witnessFuel =>
        exact ⟨witnessFuel, Nat.le_trans (Nat.le_succ _)
          hwitnessFuelLe, by
          simpa [PartialTyCoherentWitness] using hinnerBox⟩
  · intro _lv mutable targets _borrowLifetime _targetLifetime targetTy
      _hborrow htargets ihBorrow _ihTargets
    rcases ihBorrow with
      ⟨borrowWitnessFuel, hborrowWitnessFuelLe, hborrowWitness⟩
    cases borrowWitnessFuel with
    | zero =>
        exact False.elim hborrowWitness
    | succ borrowWitnessFuel =>
        rcases hborrowWitness with
          ⟨witnessTargetTy, witnessTargetLifetime, hwitnessTargets,
            hwitnessTargetTy⟩
        rcases LValTargetsTyping.output_full htargets with
          ⟨actualTargetTy, htargetTyEq⟩
        subst htargetTyEq
        have hlinearForRanks := hlinear
        rcases hlinearForRanks with ⟨φ, hφ⟩
        have heqvTargets :
            PartialTy.eqv (.ty witnessTargetTy) (.ty actualTargetTy) :=
          lvalTargetsTyping_eqv_of_subset_of_lval_eqv
            (env := env)
            (leftTargets := targets) (rightTargets := targets)
            (leftTy := .ty witnessTargetTy) (rightTy := .ty actualTargetTy)
            (leftLifetime := witnessTargetLifetime)
            (rightLifetime := _targetLifetime)
            (fun hleft hright =>
              lvalTyping_eqv_of_linearizedBy hφ hleft hright)
            hwitnessTargets htargets
            (by intro target htarget; exact htarget)
            (by intro target htarget; exact htarget)
        exact ⟨borrowWitnessFuel,
          Nat.le_trans (Nat.le_succ _) hborrowWitnessFuelLe,
          partialTyCoherentWitness_of_eqv hlinear heqvTargets
            (by
              simpa [PartialTyCoherentWitness] using hwitnessTargetTy)⟩
  · intro _target _ty _targetLifetime _htyping _ihTyping
    trivial
  · intro _target _rest _headTy _headLifetime _restLifetime _lifetime
      _restTy _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
    trivial

private def CoherentNonemptyWitness (fuel : Nat) (env : Env) : Prop :=
  ∀ {name : Name} {slot : EnvSlot},
    env.slotAt name = some slot →
      PartialTyCoherentNonemptyWitness fuel env slot.ty

private theorem coherentNonempty_witness_sound {fuel : Nat} {env : FiniteEnv} :
    coherentNonempty fuel env = true →
      CoherentNonemptyWitness fuel env.toEnv := by
  intro hcoherent name slot hslot
  have hentry : (name, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  unfold coherentNonempty at hcoherent
  have hentryCheck :=
    (List.all_eq_true.mp hcoherent) (name, slot) hentry
  exact (coherentNonemptyWitness_sound fuel).2 hentryCheck

private theorem coherentNonemptyWitness_lvalTyping_witness {fuel : Nat}
    {env : Env}
    (hwitness : CoherentNonemptyWitness fuel env)
    (hlinear : Linearizable env) :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LValTyping env lv partialTy lifetime →
        ∃ witnessFuel,
          witnessFuel ≤ fuel ∧
            PartialTyCoherentNonemptyWitness witnessFuel env partialTy := by
  intro lv partialTy lifetime htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy _lifetime _ =>
      ∃ witnessFuel,
        witnessFuel ≤ fuel ∧
          PartialTyCoherentNonemptyWitness witnessFuel env partialTy)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    ?var ?box ?borrow ?singleton ?cons htyping
  · intro _x _slot hslot
    exact ⟨fuel, Nat.le_refl fuel, hwitness hslot⟩
  · intro _lv inner _lifetime _htyping ih
    rcases ih with ⟨witnessFuel, hwitnessFuelLe, hinnerBox⟩
    cases witnessFuel with
    | zero =>
        exact False.elim hinnerBox
    | succ witnessFuel =>
        exact ⟨witnessFuel, Nat.le_trans (Nat.le_succ _)
          hwitnessFuelLe, by
          simpa [PartialTyCoherentNonemptyWitness] using hinnerBox⟩
  · intro _lv mutable targets _borrowLifetime targetLifetime targetTy
      _hborrow htargets ihBorrow _ihTargets
    rcases ihBorrow with
      ⟨borrowWitnessFuel, hborrowWitnessFuelLe, hborrowWitness⟩
    cases borrowWitnessFuel with
    | zero =>
        have htargetsEmpty : targets = [] := hborrowWitness
        subst htargetsEmpty
        exact False.elim (LValTargetsTyping.nil_false htargets)
    | succ borrowWitnessFuel =>
        cases hborrowWitness with
        | inl htargetsEmpty =>
            subst htargetsEmpty
            exact False.elim (LValTargetsTyping.nil_false htargets)
        | inr hborrowWitnessNonempty =>
            rcases hborrowWitnessNonempty with
              ⟨witnessTargetTy, witnessTargetLifetime, hwitnessTargets,
                hwitnessTargetTy⟩
            rcases LValTargetsTyping.output_full htargets with
              ⟨actualTargetTy, htargetTyEq⟩
            subst htargetTyEq
            have hlinearForRanks := hlinear
            rcases hlinearForRanks with ⟨φ, hφ⟩
            have heqvTargets :
                PartialTy.eqv (.ty witnessTargetTy) (.ty actualTargetTy) :=
              lvalTargetsTyping_eqv_of_subset_of_lval_eqv
                (env := env)
                (leftTargets := targets) (rightTargets := targets)
                (leftTy := .ty witnessTargetTy) (rightTy := .ty actualTargetTy)
                (leftLifetime := witnessTargetLifetime)
                (rightLifetime := targetLifetime)
                (fun hleft hright =>
                  lvalTyping_eqv_of_linearizedBy hφ hleft hright)
                hwitnessTargets htargets
                (by intro target htarget; exact htarget)
                (by intro target htarget; exact htarget)
            exact ⟨borrowWitnessFuel,
              Nat.le_trans (Nat.le_succ _) hborrowWitnessFuelLe,
              partialTyCoherentNonemptyWitness_of_eqv hlinear heqvTargets
                (by
                  simpa [PartialTyCoherentNonemptyWitness] using
                    hwitnessTargetTy)⟩
  · intro _target _ty _targetLifetime _htyping _ihTyping
    trivial
  · intro _target _rest _headTy _headLifetime _restLifetime _lifetime
      _restTy _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
    trivial

private theorem coherentNonempty_lvalTyping_sound {fuel : Nat}
    {env : FiniteEnv} :
    coherentNonempty fuel env = true →
    Linearizable env.toEnv →
    ∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
      {borrowLifetime : Lifetime},
      LValTyping env.toEnv lv (.ty (.borrow mutable targets)) borrowLifetime →
      targets ≠ [] →
        ∃ targetTy targetLifetime,
          LValTargetsTyping env.toEnv targets (.ty targetTy) targetLifetime := by
  intro hcoherent hlinear lv mutable targets borrowLifetime htyping hnonempty
  rcases coherentNonemptyWitness_lvalTyping_witness
      (coherentNonempty_witness_sound hcoherent) hlinear htyping with
    ⟨witnessFuel, _hle, hpartialWitness⟩
  exact partialTyCoherentNonemptyWitness_contains_borrow_targets
    hpartialWitness PartialTyContains.here hnonempty

private theorem rootCoherent_lvalTyping_witness {fuel : Nat}
    {env : Env} {root : Name}
    (hrootWitness :
      ∀ {slot : EnvSlot},
        env.slotAt root = some slot →
          PartialTyCoherentWitness fuel env slot.ty)
    (hlinear : Linearizable env) :
    ∀ {lv : LVal} {partialTy : PartialTy} {lifetime : Lifetime},
      LVal.base lv = root →
      LValTyping env lv partialTy lifetime →
        ∃ witnessFuel,
          witnessFuel ≤ fuel ∧
            PartialTyCoherentWitness witnessFuel env partialTy := by
  intro lv partialTy lifetime hbase htyping
  refine LValTyping.rec
    (motive_1 := fun lv partialTy _lifetime _ =>
      LVal.base lv = root →
        ∃ witnessFuel,
          witnessFuel ≤ fuel ∧
            PartialTyCoherentWitness witnessFuel env partialTy)
    (motive_2 := fun _targets _partialTy _lifetime _ => True)
    ?var ?box ?borrow ?singleton ?cons htyping hbase
  · intro x slot hslot hbase
    have hx : x = root := by
      simpa [LVal.base] using hbase
    subst hx
    exact ⟨fuel, Nat.le_refl fuel, hrootWitness hslot⟩
  · intro lv inner _lifetime _htyping ih hbase
    have hsourceBase : LVal.base lv = root := by
      simpa [LVal.base] using hbase
    rcases ih hsourceBase with ⟨witnessFuel, hwitnessFuelLe, hinnerBox⟩
    cases witnessFuel with
    | zero =>
        exact False.elim hinnerBox
    | succ witnessFuel =>
        exact ⟨witnessFuel, Nat.le_trans (Nat.le_succ _)
          hwitnessFuelLe, by
          simpa [PartialTyCoherentWitness] using hinnerBox⟩
  · intro lv mutable targets _borrowLifetime targetLifetime targetTy
      _hborrow htargets ihBorrow _ihTargets hbase
    have hsourceBase : LVal.base lv = root := by
      simpa [LVal.base] using hbase
    rcases ihBorrow hsourceBase with
      ⟨borrowWitnessFuel, hborrowWitnessFuelLe, hborrowWitness⟩
    cases borrowWitnessFuel with
    | zero =>
        exact False.elim hborrowWitness
    | succ borrowWitnessFuel =>
        rcases hborrowWitness with
          ⟨witnessTargetTy, witnessTargetLifetime, hwitnessTargets,
            hwitnessTargetTy⟩
        rcases LValTargetsTyping.output_full htargets with
          ⟨actualTargetTy, htargetTyEq⟩
        subst htargetTyEq
        have hlinearForRanks := hlinear
        rcases hlinearForRanks with ⟨φ, hφ⟩
        have heqvTargets :
            PartialTy.eqv (.ty witnessTargetTy) (.ty actualTargetTy) :=
          lvalTargetsTyping_eqv_of_subset_of_lval_eqv
            (env := env)
            (leftTargets := targets) (rightTargets := targets)
            (leftTy := .ty witnessTargetTy) (rightTy := .ty actualTargetTy)
            (leftLifetime := witnessTargetLifetime)
            (rightLifetime := targetLifetime)
            (fun hleft hright =>
              lvalTyping_eqv_of_linearizedBy hφ hleft hright)
            hwitnessTargets htargets
            (by intro target htarget; exact htarget)
            (by intro target htarget; exact htarget)
        exact ⟨borrowWitnessFuel,
          Nat.le_trans (Nat.le_succ _) hborrowWitnessFuelLe,
          partialTyCoherentWitness_of_eqv hlinear heqvTargets
            (by
              simpa [PartialTyCoherentWitness] using hwitnessTargetTy)⟩
  · intro _target _ty _targetLifetime _htyping _ihTyping
    trivial
  · intro _target _rest _headTy _headLifetime _restLifetime _lifetime
      _restTy _unionTy _hhead _hrest _hunion _hintersection _ihHead _ihRest
    trivial

private theorem rootCoherent_written_root_sound {fuel : Nat}
    {env : FiniteEnv} {root : Name} :
    rootCoherent fuel env root = true →
    Linearizable env.toEnv →
    ∀ {lv : LVal} {mutable : Bool} {targets : List LVal}
      {borrowLifetime : Lifetime},
      LVal.base lv = root →
      LValTyping env.toEnv lv (.ty (.borrow mutable targets)) borrowLifetime →
        ∃ targetTy targetLifetime,
          LValTargetsTyping env.toEnv targets (.ty targetTy) targetLifetime := by
  intro hroot hlinear lv mutable targets borrowLifetime hbase htyping
  rcases rootCoherent_lvalTyping_witness
      (env := env.toEnv) (root := root)
      (by
        intro slot hslot
        exact rootCoherent_witness_sound hroot hslot)
      hlinear hbase htyping with
    ⟨witnessFuel, _hle, hpartialWitness⟩
  exact partialTyCoherentWitness_contains_borrow_targets
    hpartialWitness PartialTyContains.here

private theorem coherentWitness_sound_coherent {fuel : Nat} {env : Env} :
    CoherentWitness fuel env →
    Linearizable env →
      Coherent env := by
  intro hwitness hlinear lv mutable targets borrowLifetime htyping
  rcases coherentWitness_lvalTyping_witness hwitness hlinear htyping with
    ⟨witnessFuel, _hle, hpartialWitness⟩
  exact partialTyCoherentWitness_contains_borrow_targets
    hpartialWitness PartialTyContains.here

private theorem coherentWitness_slot_contains_borrow_targets
    {fuel : Nat} {env : Env} {name : Name} {slot : EnvSlot}
    {mutable : Bool} {targets : List LVal} :
    CoherentWitness fuel env →
      env.slotAt name = some slot →
        PartialTyContains slot.ty (.borrow mutable targets) →
          ∃ targetTy targetLifetime,
            LValTargetsTyping env targets (.ty targetTy) targetLifetime := by
  intro hwitness hslot hcontains
  exact partialTyCoherentWitness_contains_borrow_targets
    (hwitness hslot) hcontains

private theorem support_foldl_preserves {entries : List (Name × EnvSlot)}
    {acc : List Name} {name : Name} :
    name ∈ acc →
      name ∈ entries.foldl
        (fun names entry =>
          if names.contains entry.1 then names else names ++ [entry.1])
        acc := by
  induction entries generalizing acc with
  | nil =>
      intro h
      exact h
  | cons entry rest ih =>
      intro h
      apply ih
      by_cases hcontains : acc.contains entry.1
      · have hentryMem : entry.1 ∈ acc := by
          simpa using hcontains
        simpa [hentryMem] using h
      · have hentryNotMem : entry.1 ∉ acc := by
          simpa using hcontains
        simpa [hentryNotMem] using List.mem_append_left [entry.1] h

private theorem support_foldl_contains_entry
    {entries : List (Name × EnvSlot)} {acc : List Name}
    {entry : Name × EnvSlot} :
    entry ∈ entries →
      entry.1 ∈ entries.foldl
        (fun names entry =>
          if names.contains entry.1 then names else names ++ [entry.1])
        acc := by
  induction entries generalizing acc with
  | nil =>
      intro h
      cases h
  | cons first rest ih =>
      intro h
      cases h with
      | head =>
        apply support_foldl_preserves (entries := rest)
          (acc := if acc.contains entry.1 then acc else acc ++ [entry.1])
        by_cases hmem : entry.1 ∈ acc
        · simp [hmem]
        · simp [hmem]
      | tail _ hrest =>
        exact ih (acc :=
          if acc.contains first.1 then acc else acc ++ [first.1]) hrest

private theorem lookup_mem_support {env : FiniteEnv} {name : Name}
    {slot : EnvSlot} :
    env.lookup name = some slot → name ∈ env.support := by
  intro hlookup
  cases env with
  | mk entries =>
      change FiniteEnv.lookupEntries entries name = some slot at hlookup
      change name ∈
        entries.foldl
          (fun names entry =>
            if names.contains entry.1 then names else names ++ [entry.1])
          []
      exact support_foldl_contains_entry (lookupEntries_mem hlookup)

private theorem lookup_update_eq (env : FiniteEnv) (name : Name)
    (slot : EnvSlot) :
    (env.update name slot).lookup name = some slot := by
  have h := congrArg (fun env => env.slotAt name)
    (FiniteEnv.toEnv_update env name slot)
  simpa [FiniteEnv.toEnv, Env.update] using h

private theorem lookup_update_ne (env : FiniteEnv) {updated name : Name}
    (slot : EnvSlot) (hne : name ≠ updated) :
    (env.update updated slot).lookup name = env.lookup name := by
  have h := congrArg (fun env => env.slotAt name)
    (FiniteEnv.toEnv_update env updated slot)
  simpa [FiniteEnv.toEnv, Env.update, hne] using h

private theorem support_foldl_mem_iff
    {entries : List (Name × EnvSlot)} {acc : List Name} {name : Name} :
    name ∈ entries.foldl
        (fun names entry =>
          if names.contains entry.1 then names else names ++ [entry.1])
        acc ↔
      name ∈ acc ∨ ∃ slot, (name, slot) ∈ entries := by
  induction entries generalizing acc with
  | nil =>
      simp
  | cons entry rest ih =>
      rcases entry with ⟨entryName, entrySlot⟩
      have hstep :
          name ∈
              (if acc.contains entryName then acc else acc ++ [entryName]) ↔
            name ∈ acc ∨ name = entryName := by
        by_cases hentryMem : entryName ∈ acc
        · have hif :
            (if acc.contains entryName then acc else acc ++ [entryName]) =
              acc := by
              simp [hentryMem]
          rw [hif]
          constructor
          · intro hmem
            exact Or.inl hmem
          · intro hmem
            rcases hmem with hmem | hmem
            · exact hmem
            · subst hmem
              exact hentryMem
        · have hif :
            (if acc.contains entryName then acc else acc ++ [entryName]) =
              acc ++ [entryName] := by
              simp [hentryMem]
          rw [hif]
          constructor
          · intro hmem
            rcases List.mem_append.mp hmem with hmemAcc | hmemSingle
            · exact Or.inl hmemAcc
            · simp at hmemSingle
              exact Or.inr hmemSingle
          · intro hmem
            rcases hmem with hmem | hmem
            · exact List.mem_append_left [entryName] hmem
            · subst hmem
              exact List.mem_append_right acc (by simp)
      change name ∈
          rest.foldl
            (fun names entry =>
              if names.contains entry.1 then names else names ++ [entry.1])
            (if acc.contains entryName then acc else acc ++ [entryName]) ↔
        name ∈ acc ∨ ∃ slot, (name, slot) ∈ (entryName, entrySlot) :: rest
      rw [ih]
      constructor
      · intro hmem
        rcases hmem with hmem | hmem
        · rcases hstep.mp hmem with hmemAcc | hname
          · exact Or.inl hmemAcc
          · subst hname
            exact Or.inr ⟨entrySlot, List.mem_cons_self⟩
        · rcases hmem with ⟨slot, hslot⟩
          exact Or.inr ⟨slot, List.mem_cons_of_mem _ hslot⟩
      · intro hmem
        rcases hmem with hmemAcc | hentry
        · exact Or.inl (hstep.mpr (Or.inl hmemAcc))
        · rcases hentry with ⟨slot, hslot⟩
          cases hslot with
          | head =>
              exact Or.inl (hstep.mpr (Or.inr rfl))
          | tail _ htail =>
              exact Or.inr ⟨slot, htail⟩

private theorem lookupEntries_isSome_of_entry_name
    {entries : List (Name × EnvSlot)} {name : Name} {slot : EnvSlot} :
    (name, slot) ∈ entries →
      ∃ found, FiniteEnv.lookupEntries entries name = some found := by
  intro hmem
  induction entries with
  | nil =>
      cases hmem
  | cons entry rest ih =>
      rcases entry with ⟨entryName, entrySlot⟩
      cases hmem with
      | head =>
          simp [FiniteEnv.lookupEntries]
      | tail _ htail =>
          by_cases hname : name = entryName
          · subst hname
            exact ⟨entrySlot, by simp [FiniteEnv.lookupEntries]⟩
          · rcases ih htail with ⟨found, hfound⟩
            exact ⟨found, by simpa [FiniteEnv.lookupEntries, hname] using hfound⟩

private theorem mem_support_iff_lookup_isSome {env : FiniteEnv}
    {name : Name} :
    name ∈ env.support ↔ ∃ slot, env.lookup name = some slot := by
  constructor
  · intro hmem
    cases env with
    | mk entries =>
        change name ∈
          entries.foldl
            (fun names entry =>
              if names.contains entry.1 then names else names ++ [entry.1])
            [] at hmem
        rcases (support_foldl_mem_iff.mp hmem) with hnil | hentry
        · cases hnil
        · rcases hentry with ⟨slot, hentry⟩
          exact lookupEntries_isSome_of_entry_name hentry
  · intro hlookup
    rcases hlookup with ⟨slot, hslot⟩
    exact lookup_mem_support hslot

private theorem lookup_none_of_not_mem_support {env : FiniteEnv}
    {name : Name} :
    name ∉ env.support → env.lookup name = none := by
  intro hnot
  cases hlookup : env.lookup name with
  | none => rfl
  | some slot =>
      exact False.elim (hnot (lookup_mem_support hlookup))

private theorem sameBindings_lookup_eq {left right : FiniteEnv} :
    left.sameBindings right = true →
      ∀ name, left.lookup name = right.lookup name := by
  intro h name
  unfold FiniteEnv.sameBindings at h
  let names := unionNames left.support right.support
  by_cases hmem : name ∈ names
  · have hcheck := (List.all_eq_true.mp h) name hmem
    by_cases heq : left.lookup name = right.lookup name
    · exact heq
    · simp [heq] at hcheck
  · have hnotLeft : name ∉ left.support := by
      intro hleft
      exact hmem ((mem_unionNames).mpr (Or.inl hleft))
    have hnotRight : name ∉ right.support := by
      intro hright
      exact hmem ((mem_unionNames).mpr (Or.inr hright))
    rw [lookup_none_of_not_mem_support hnotLeft,
      lookup_none_of_not_mem_support hnotRight]

private theorem envEqOutside_lookup_eq {left right : FiniteEnv}
    {exceptName : Name} :
    envEqOutside left right exceptName = true →
      ∀ name, name ≠ exceptName → left.lookup name = right.lookup name := by
  intro h name hne
  unfold envEqOutside at h
  let names := unionNames left.support right.support
  by_cases hmem : name ∈ names
  · have hcheck := (List.all_eq_true.mp h) name hmem
    have hnotExcept : ¬ name = exceptName := hne
    simp [hnotExcept] at hcheck
    by_cases heq : left.lookup name = right.lookup name
    · exact heq
    · simp [heq] at hcheck
  · have hnotLeft : name ∉ left.support := by
      intro hleft
      exact hmem ((mem_unionNames).mpr (Or.inl hleft))
    have hnotRight : name ∉ right.support := by
      intro hright
      exact hmem ((mem_unionNames).mpr (Or.inr hright))
    rw [lookup_none_of_not_mem_support hnotLeft,
      lookup_none_of_not_mem_support hnotRight]

private theorem sameBindings_toEnv_eq {left right : FiniteEnv} :
    left.sameBindings right = true → left.toEnv = right.toEnv := by
  intro h
  change ({ slotAt := left.lookup } : Env) = { slotAt := right.lookup }
  have hslot : left.lookup = right.lookup := by
    funext name
    exact sameBindings_lookup_eq h name
  rw [hslot]

private theorem checkResult_matches_sound {result : CheckResult}
    {expectedTy : Ty} {expectedEnv : FiniteEnv} :
    result.matches expectedTy expectedEnv = true →
      result.ty = expectedTy ∧ result.env.toEnv = expectedEnv.toEnv := by
  intro h
  unfold CheckResult.matches at h
  by_cases hty : result.ty = expectedTy
  · simp [hty] at h
    exact ⟨hty, sameBindings_toEnv_eq h⟩
  · simp [hty] at h

mutual
  private theorem updateAtPath?_sound :
      ∀ {fuel rank : Nat} {env : FiniteEnv} {path : Path}
        {oldTy : PartialTy} {rhsTy : Ty} {out : FiniteEnv}
        {updatedTy : PartialTy},
        updateAtPath? fuel rank env path oldTy rhsTy =
          some (out, updatedTy) →
          UpdateAtPath rank env.toEnv path oldTy rhsTy out.toEnv updatedTy := by
    intro fuel rank env path oldTy rhsTy out updatedTy h
    cases fuel with
    | zero =>
        simp [updateAtPath?] at h
    | succ fuel =>
        cases path with
        | nil =>
            cases rank with
            | zero =>
                simp [updateAtPath?] at h
                rcases h with ⟨rfl, rfl⟩
                exact UpdateAtPath.strong
            | succ rank =>
                cases hshape :
                    shapeCompatiblePartialTy fuel env oldTy (.ty rhsTy) with
                | false =>
                    simp [updateAtPath?, hshape] at h
                | true =>
                    cases hjoin : partialTyJoin? oldTy (.ty rhsTy) with
                    | none =>
                        simp [updateAtPath?, hshape, hjoin] at h
                    | some joined =>
                        simp [updateAtPath?, hshape, hjoin] at h
                        rcases h with ⟨rfl, rfl⟩
                        exact UpdateAtPath.weak
                          (shapeCompatiblePartialTy_sound hshape)
                          (partialTyJoin?_sound hjoin)
        | cons head rest =>
            cases head
            cases oldTy with
            | ty ty =>
                cases ty with
                | borrow mutable targets =>
                    cases mutable with
                    | false =>
                        simp [updateAtPath?] at h
                    | true =>
                        cases hwrite :
                            writeBorrowTargets? fuel (rank + 1) env rest targets
                              rhsTy with
                        | none =>
                            simp [updateAtPath?, hwrite] at h
                        | some writeEnv =>
                            simp [updateAtPath?, hwrite] at h
                            rcases h with ⟨rfl, rfl⟩
                            simpa using UpdateAtPath.mutBorrow
                              (writeBorrowTargets?_sound hwrite)
                | unit =>
                    simp [updateAtPath?] at h
                | int =>
                    simp [updateAtPath?] at h
                | box inner =>
                    simp [updateAtPath?] at h
                | bool =>
                    simp [updateAtPath?] at h
            | box inner =>
                cases hinner :
                    updateAtPath? fuel rank env rest inner rhsTy with
                | none =>
                    simp [updateAtPath?, hinner] at h
                | some result =>
                    rcases result with ⟨innerEnv, updatedInner⟩
                    simp [updateAtPath?, hinner] at h
                    rcases h with ⟨rfl, rfl⟩
                    simpa using UpdateAtPath.box (updateAtPath?_sound hinner)
            | undef ty =>
                simp [updateAtPath?] at h
  termination_by fuel rank env path oldTy rhsTy out updatedTy h => (fuel, 0, 0)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      first
      | omega
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))

  private theorem writeBorrowTargets?_sound :
      ∀ {fuel rank : Nat} {env : FiniteEnv} {path : Path}
        {targets : List LVal} {rhsTy : Ty} {out : FiniteEnv},
        writeBorrowTargets? fuel rank env path targets rhsTy = some out →
          WriteBorrowTargets rank env.toEnv path targets rhsTy out.toEnv := by
    intro fuel rank env path targets rhsTy out h
    cases targets with
    | nil =>
        simp [writeBorrowTargets?] at h
        cases h
        exact WriteBorrowTargets.nil
    | cons target rest =>
        cases rest with
        | nil =>
            cases htype : lvalType? fuel env (prependPath path target) with
            | none =>
                simp [writeBorrowTargets?, htype] at h
            | some typed =>
                rcases typed with ⟨partialTy, leafLifetime⟩
                cases partialTy with
                | ty leafTy =>
                    cases hwrite :
                        envWrite? fuel rank env (prependPath path target)
                          rhsTy with
                    | none =>
                        simp [writeBorrowTargets?, htype, hwrite] at h
                    | some updated =>
                        simp [writeBorrowTargets?, htype, hwrite] at h
                        cases h
                        exact WriteBorrowTargets.singleton
                          (envWrite?_sound hwrite)
                          ⟨leafTy, leafLifetime, lvalType?_sound htype⟩
                | box inner =>
                    simp [writeBorrowTargets?, htype] at h
                | undef ty =>
                    simp [writeBorrowTargets?, htype] at h
        | cons restHead restTail =>
            cases htype : lvalType? fuel env (prependPath path target) with
            | none =>
                simp [writeBorrowTargets?, htype] at h
            | some typed =>
                rcases typed with ⟨partialTy, leafLifetime⟩
                cases partialTy with
                | ty leafTy =>
                    cases hwrite :
                        envWrite? fuel rank env (prependPath path target)
                          rhsTy with
                    | none =>
                        simp [writeBorrowTargets?, htype, hwrite] at h
                    | some updated =>
                        cases hrest :
                            writeBorrowTargets? fuel rank env path
                              (restHead :: restTail) rhsTy with
                        | none =>
                            simp [writeBorrowTargets?, htype, hwrite, hrest] at h
                        | some restUpdated =>
                            cases hjoin : envJoin? updated restUpdated with
                            | none =>
                                simp [writeBorrowTargets?, htype, hwrite, hrest,
                                  hjoin] at h
                            | some joined =>
                                simp [writeBorrowTargets?, htype, hwrite, hrest,
                                  hjoin] at h
                                cases h
                                exact WriteBorrowTargets.cons
                                  (envWrite?_sound hwrite)
                                  ⟨leafTy, leafLifetime, lvalType?_sound htype⟩
                                  (writeBorrowTargets?_sound hrest)
                                  (envJoin?_sound hjoin)
                | box inner =>
                    simp [writeBorrowTargets?, htype] at h
                | undef ty =>
                    simp [writeBorrowTargets?, htype] at h
  termination_by fuel rank env path targets rhsTy out h => (fuel, 2, targets.length)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      first
      | omega
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))

  private theorem envWrite?_sound :
      ∀ {fuel rank : Nat} {env : FiniteEnv} {lv : LVal}
        {rhsTy : Ty} {out : FiniteEnv},
        envWrite? fuel rank env lv rhsTy = some out →
          EnvWrite rank env.toEnv lv rhsTy out.toEnv := by
    intro fuel rank env lv rhsTy out h
    unfold envWrite? at h
    cases hslot : env.lookup (LVal.base lv) with
    | none =>
        simp [hslot] at h
    | some slot =>
        cases hupdate :
            updateAtPath? fuel rank env (LVal.path lv) slot.ty rhsTy with
        | none =>
            simp [hslot, hupdate] at h
        | some result =>
            rcases result with ⟨writeEnv, updatedTy⟩
            simp [hslot, hupdate] at h
            cases h
            have hwrite :
                EnvWrite rank env.toEnv lv rhsTy
                  (writeEnv.toEnv.update (LVal.base lv)
                    { slot with ty := updatedTy }) :=
              EnvWrite.intro
                (show env.toEnv.slotAt (LVal.base lv) = some slot from hslot)
                (updateAtPath?_sound hupdate)
            simpa [FiniteEnv.toEnv_update] using hwrite
  termination_by fuel rank env lv rhsTy out h => (fuel, 1, 0)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      first
      | omega
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))
end

private theorem linearizable_rankOf_sound {env : FiniteEnv} :
    linearizable env = true →
      LinearizedBy
        (fun name => (rankOf? ((envNames env).length + 1) env name).getD 0)
        env.toEnv := by
  intro h
  let fuel := (envNames env).length + 1
  intro x slot hslot v hv
  unfold linearizable at h
  have hentry : (x, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  have hentryCheck := (List.all_eq_true.mp h) (x, slot) hentry
  change
    (match rankOf? fuel env x with
    | none => false
    | some rootRank =>
        (PartialTy.vars slot.ty).all (fun dep =>
          match rankOf? fuel env dep with
          | some depRank => depRank < rootRank
          | none => false)) = true at hentryCheck
  cases hroot : rankOf? fuel env x with
  | none =>
      simp [hroot] at hentryCheck
  | some rootRank =>
      simp [hroot] at hentryCheck
      have hdepCheck := hentryCheck v hv
      cases hdep : rankOf? fuel env v with
      | none =>
          simp [hdep] at hdepCheck
        | some depRank =>
            simp [hdep] at hdepCheck
            simpa [fuel, hroot, hdep]
              using hdepCheck

private theorem linearizable_sound {env : FiniteEnv} :
    linearizable env = true → Linearizable env.toEnv := by
  intro h
  exact ⟨fun name => (rankOf? ((envNames env).length + 1) env name).getD 0,
    linearizable_rankOf_sound h⟩

private theorem linearizedByRanks?_sound {fuel : Nat}
    {rankSource env : FiniteEnv} :
    linearizedByRanks? fuel rankSource env = true →
      LinearizedBy
        (fun name => (rankOf? fuel rankSource name).getD 0)
        env.toEnv := by
  intro h x slot hslot v hv
  unfold linearizedByRanks? at h
  have hentry : (x, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  have hentryCheck := (List.all_eq_true.mp h) (x, slot) hentry
  change
    (match rankOf? fuel rankSource x with
    | none => false
    | some rootRank =>
        (PartialTy.vars slot.ty).all (fun dep =>
          match rankOf? fuel rankSource dep with
          | some depRank => depRank < rootRank
          | none => false)) = true at hentryCheck
  cases hroot : rankOf? fuel rankSource x with
  | none =>
      simp [hroot] at hentryCheck
  | some rootRank =>
      simp [hroot] at hentryCheck
      have hdepCheck := hentryCheck v hv
      cases hdep : rankOf? fuel rankSource v with
      | none =>
          simp [hdep] at hdepCheck
      | some depRank =>
          simp [hdep] at hdepCheck
          simpa [hroot, hdep] using hdepCheck

private theorem partialTyContainsBorrow_mem_aux {partialTy : PartialTy}
    {needle : Ty}
    (hcontains : PartialTyContains partialTy needle) :
    ∀ {mutable : Bool} {targets : List LVal},
      needle = .borrow mutable targets →
        (mutable, targets) ∈ partialTyBorrows partialTy := by
  induction hcontains with
  | here =>
      intro mutable targets hneedle
      cases hneedle
      simp [partialTyBorrows, tyBorrows]
  | tyBox _ ih =>
      intro mutable targets hneedle
      simpa [partialTyBorrows, tyBorrows] using ih hneedle
  | box _ ih =>
      intro mutable targets hneedle
      simpa [partialTyBorrows] using ih hneedle

private theorem partialTyContainsBorrow_mem {partialTy : PartialTy}
    {mutable : Bool} {targets : List LVal} :
    PartialTyContains partialTy (.borrow mutable targets) →
      (mutable, targets) ∈ partialTyBorrows partialTy := by
  intro hcontains
  exact partialTyContainsBorrow_mem_aux hcontains rfl

mutual
  private theorem tyContainsBorrow_of_mem :
      ∀ {ty : Ty} {mutable : Bool} {targets : List LVal},
        (mutable, targets) ∈ tyBorrows ty →
          PartialTyContains (.ty ty) (.borrow mutable targets) := by
    intro ty mutable targets h
    cases ty with
    | unit =>
        simp [tyBorrows] at h
    | int =>
        simp [tyBorrows] at h
    | bool =>
        simp [tyBorrows] at h
    | borrow borrowMutable borrowTargets =>
        simp [tyBorrows] at h
        rcases h with ⟨rfl, rfl⟩
        exact PartialTyContains.here
    | box inner =>
        exact PartialTyContains.tyBox
          (tyContainsBorrow_of_mem (by simpa [tyBorrows] using h))

  private theorem partialTyContainsBorrow_of_mem :
      ∀ {partialTy : PartialTy} {mutable : Bool} {targets : List LVal},
        (mutable, targets) ∈ partialTyBorrows partialTy →
          PartialTyContains partialTy (.borrow mutable targets) := by
    intro partialTy mutable targets h
    cases partialTy with
    | ty ty =>
        exact tyContainsBorrow_of_mem h
    | box inner =>
        exact PartialTyContains.box
          (partialTyContainsBorrow_of_mem
            (by simpa [partialTyBorrows] using h))
    | undef ty =>
        simp [partialTyBorrows] at h
end

private theorem lvalMem_true_of_mem {target : LVal} :
    ∀ {targets : List LVal}, target ∈ targets → lvalMem target targets = true
  | [], h => by cases h
  | head :: rest, h => by
      cases h with
      | head =>
          simp [lvalMem]
      | tail _ htail =>
          by_cases heq : target = head
          · simp [lvalMem, heq]
          · simp [lvalMem, heq, lvalMem_true_of_mem htail]

private theorem targetInBorrowTargets_true {target : LVal} {rhsTy : Ty} :
    (∃ rhsMutable rhsTargets,
      PartialTyContains (.ty rhsTy) (.borrow rhsMutable rhsTargets) ∧
        target ∈ rhsTargets) →
      targetInBorrowTargets target (tyBorrows rhsTy) = true := by
  rintro ⟨rhsMutable, rhsTargets, hcontains, htarget⟩
  unfold targetInBorrowTargets
  rw [List.any_eq_true]
  refine ⟨(rhsMutable, rhsTargets), ?_, ?_⟩
  · simpa [partialTyBorrows] using partialTyContainsBorrow_mem hcontains
  · exact lvalMem_true_of_mem htarget

private theorem containedBorrowsWellFormed_sound {fuel : Nat}
    {env : FiniteEnv} :
    containedBorrowsWellFormed fuel env = true →
      ContainedBorrowsWellFormed env.toEnv := by
  intro h x slot mutable targets hslot hcontains
  rcases hcontains with ⟨containedSlot, hcontainedSlot, hcontainsTy⟩
  have hcontainedEq : containedSlot = slot :=
    Option.some.inj (hcontainedSlot.symm.trans hslot)
  subst containedSlot
  cases env with
  | mk entries =>
      have hentry : (x, slot) ∈ entries :=
        lookupEntries_mem hslot
      unfold containedBorrowsWellFormed at h
      have hentryCheck := (List.all_eq_true.mp h) (x, slot) hentry
      have hborrowMem :
          (mutable, targets) ∈ partialTyBorrows slot.ty :=
        partialTyContainsBorrow_mem hcontainsTy
      have htargetsCheck :=
        (List.all_eq_true.mp hentryCheck) (mutable, targets) hborrowMem
      exact BorrowTargetsWellFormed.inSlot
        (borrowTargetsWellFormed_sound htargetsCheck)

private theorem coherent_slot_borrow_targets_sound {fuel : Nat}
    {env : FiniteEnv} {name : Name} {slot : EnvSlot}
    {mutable : Bool} {targets : List LVal} :
    coherent fuel env = true →
      env.lookup name = some slot →
        slot.ty = .ty (.borrow mutable targets) →
          ∃ targetTy targetLifetime,
            LValTargetsTyping env.toEnv targets (.ty targetTy)
              targetLifetime := by
  intro hcoherent hslot hslotTy
  have hentry : (name, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  unfold coherent at hcoherent
  have hentryCheck :=
    (List.all_eq_true.mp hcoherent) (name, slot) hentry
  rw [hslotTy] at hentryCheck
  exact tyCoherent_borrow_targets_sound
    (by simpa [partialTyCoherent] using hentryCheck)

private theorem coherent_slot_contains_borrow_targets_sound {fuel : Nat}
    {env : FiniteEnv} {name : Name} {slot : EnvSlot}
    {mutable : Bool} {targets : List LVal} :
    coherent fuel env = true →
      env.lookup name = some slot →
        PartialTyContains slot.ty (.borrow mutable targets) →
          ∃ targetTy targetLifetime,
            LValTargetsTyping env.toEnv targets (.ty targetTy)
              targetLifetime := by
  intro hcoherent hslot hcontains
  have hentry : (name, slot) ∈ env.entries :=
    lookupEntries_mem hslot
  unfold coherent at hcoherent
  have hentryCheck :=
    (List.all_eq_true.mp hcoherent) (name, slot) hentry
  exact partialTyCoherent_contains_borrow_targets_sound hentryCheck hcontains rfl

private theorem wellFormedKit_sound {fuel : Nat} {env : FiniteEnv} :
    wellFormedKit fuel env = true →
      ContainedBorrowsWellFormed env.toEnv ∧
        coherent fuel env = true ∧
          Linearizable env.toEnv := by
  intro h
  unfold wellFormedKit at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hcontainedAndCoherent, hlinear⟩
  rcases Bool.and_eq_true_iff.mp hcontainedAndCoherent with
    ⟨hcontained, hcoherent⟩
  exact ⟨containedBorrowsWellFormed_sound hcontained, hcoherent,
    linearizable_sound hlinear⟩

private def CheckerInvariant (env : FiniteEnv) : Prop :=
  ContainedBorrowsWellFormed env.toEnv ∧
    Coherent env.toEnv ∧
      Linearizable env.toEnv

private theorem CheckerInvariant.empty :
    CheckerInvariant FiniteEnv.empty := by
  simp [CheckerInvariant, containedBorrowsWellFormed_empty, coherent_empty,
    linearizable_empty]

private theorem CheckerInvariant.of_wellFormedKit {fuel : Nat}
    {env : FiniteEnv} :
    wellFormedKit fuel env = true →
      CheckerInvariant env := by
  intro hkit
  have hsound := wellFormedKit_sound hkit
  exact ⟨hsound.1,
    coherentWitness_sound_coherent
      (coherent_witness_sound hsound.2.1) hsound.2.2,
    hsound.2.2⟩

private theorem wellFormedKit_coherent_witness_sound {fuel : Nat}
    {env : FiniteEnv} :
    wellFormedKit fuel env = true →
      CoherentWitness fuel env.toEnv := by
  intro hkit
  exact coherent_witness_sound (wellFormedKit_sound hkit).2.1

private theorem wellFormedKit_coherent_sound {fuel : Nat}
    {env : FiniteEnv} :
    wellFormedKit fuel env = true →
      Coherent env.toEnv := by
  intro hkit
  exact coherentWitness_sound_coherent
    (wellFormedKit_coherent_witness_sound hkit)
    (wellFormedKit_sound hkit).2.2

private theorem wellFormedKit_slot_contains_borrow_targets_sound {fuel : Nat}
    {env : FiniteEnv} {name : Name} {slot : EnvSlot}
    {mutable : Bool} {targets : List LVal} :
    wellFormedKit fuel env = true →
      env.lookup name = some slot →
        PartialTyContains slot.ty (.borrow mutable targets) →
          ∃ targetTy targetLifetime,
            LValTargetsTyping env.toEnv targets (.ty targetTy)
              targetLifetime := by
  intro hkit hslot hcontains
  exact coherent_slot_contains_borrow_targets_sound
    (wellFormedKit_sound hkit).2.1 hslot hcontains

private theorem assignmentResultInvariants_sound {fuel : Nat}
    {env : FiniteEnv} :
    (containedBorrowsWellFormed fuel env && linearizable env) = true →
      ContainedBorrowsWellFormed env.toEnv ∧ Linearizable env.toEnv := by
  intro h
  rcases Bool.and_eq_true_iff.mp h with ⟨hcontained, hlinear⟩
  exact ⟨containedBorrowsWellFormed_sound hcontained,
    linearizable_sound hlinear⟩

private theorem envBorrowEdges_mem_of_entry {entries : List (Name × EnvSlot)}
    {entry : Name × EnvSlot} {borrow : Bool × List LVal} :
    entry ∈ entries →
      borrow ∈ partialTyBorrows entry.2.ty →
        (entry.1, borrow.1, borrow.2) ∈
          entries.foldr
            (fun entry edges =>
              (partialTyBorrows entry.2.ty).map
                  (fun borrow => (entry.1, borrow.1, borrow.2)) ++ edges)
            [] := by
  intro hentry hborrow
  induction entries with
  | nil =>
      cases hentry
  | cons head rest ih =>
      cases hentry with
      | head =>
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨borrow, hborrow, rfl⟩
      | tail _ hrest =>
          exact List.mem_append_right _ (ih hrest)

private theorem envBorrowEdges_of_contains {env : FiniteEnv}
    {root : Name} {mutable : Bool} {targets : List LVal} :
    env.toEnv ⊢ root ↝ Ty.borrow mutable targets →
      (root, mutable, targets) ∈ envBorrowEdges env := by
  intro hcontains
  rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
  cases env with
  | mk entries =>
      have hentry : (root, slot) ∈ entries :=
        lookupEntries_mem hslot
      exact envBorrowEdges_mem_of_entry hentry
        (partialTyContainsBorrow_mem hcontainsTy)

private abbrev EntriesReflectLookup (env : FiniteEnv) : Prop :=
  ∀ {name : Name} {slot : EnvSlot},
    (name, slot) ∈ env.entries → env.lookup name = some slot

private theorem entriesReflectLookup_empty :
    EntriesReflectLookup FiniteEnv.empty := by
  intro name slot hmem
  cases hmem

private theorem entriesReflectLookup_update {env : FiniteEnv}
    {name : Name} {slot : EnvSlot} :
    EntriesReflectLookup env →
      EntriesReflectLookup (env.update name slot) := by
  intro hreflect needle candidate hmem
  unfold FiniteEnv.update at hmem
  simp only [List.mem_cons, List.mem_filter] at hmem
  rcases hmem with hhead | htail
  · cases hhead
    exact lookup_update_eq env name slot
  · rcases htail with ⟨horiginal, hkeep⟩
    have hne : needle ≠ name := by
      intro heq
      subst heq
      simp at hkeep
    rw [lookup_update_ne env slot hne]
    exact hreflect horiginal

private theorem entriesReflectLookup_erase {env : FiniteEnv}
    {erased : Name} :
    EntriesReflectLookup env →
      EntriesReflectLookup (env.erase erased) := by
  intro hreflect needle candidate hmem
  cases env with
  | mk entries =>
      change (needle, candidate) ∈
        entries.filter (fun entry => entry.1 != erased) at hmem
      change
        FiniteEnv.lookupEntries
          (entries.filter (fun entry => entry.1 != erased)) needle =
            some candidate
      simp only [List.mem_filter] at hmem
      rcases hmem with ⟨horiginal, hkeep⟩
      have hne : needle ≠ erased := by
        intro heq
        subst heq
        simp at hkeep
      rw [FiniteEnv.lookupEntries_filter_update_ne entries hne]
      exact hreflect horiginal

private theorem entriesReflectLookup_dropLifetime {env : FiniteEnv}
    {lifetime : Lifetime} :
    EntriesReflectLookup env →
      EntriesReflectLookup (env.dropLifetime lifetime) := by
  intro _hreflect name slot hmem
  unfold FiniteEnv.dropLifetime at hmem
  simp only [List.mem_filter] at hmem
  rcases hmem with ⟨_horiginal, hkeep⟩
  cases hlookup : env.lookup name with
  | none =>
      simp [hlookup] at hkeep
  | some candidate =>
      simp [hlookup] at hkeep
      rcases hkeep with ⟨hslot, hlifetime⟩
      subst hslot
      have hdrop := congrArg (fun env => env.slotAt name)
        (FiniteEnv.toEnv_dropLifetime env lifetime)
      change
        (env.dropLifetime lifetime).lookup name =
          (env.toEnv.dropLifetime lifetime).slotAt name at hdrop
      simpa [FiniteEnv.toEnv, Env.dropLifetime, hlookup, hlifetime] using hdrop

private theorem entriesReflectLookup_envJoinStep? {left right result out : FiniteEnv}
    {name : Name} :
    EntriesReflectLookup result →
      envJoinStep? left right result name = some out →
        EntriesReflectLookup out := by
  intro hreflect hstep
  unfold envJoinStep? at hstep
  cases hleft : left.lookup name <;>
    cases hright : right.lookup name <;> simp [hleft, hright] at hstep
  · cases hstep
    exact hreflect
  · rename_i leftSlot rightSlot
    by_cases hlife : leftSlot.lifetime = rightSlot.lifetime
    · cases hjoin : partialTyJoin? leftSlot.ty rightSlot.ty with
      | none =>
          simp [hlife, hjoin] at hstep
      | some joined =>
          simp [hlife, hjoin] at hstep
          cases hstep
          exact entriesReflectLookup_update hreflect
    · simp [hlife] at hstep

private theorem entriesReflectLookup_envJoinNames? {left right result out : FiniteEnv}
    {names : List Name} :
    EntriesReflectLookup result →
      envJoinNames? left right names result = some out →
        EntriesReflectLookup out := by
  induction names generalizing result with
  | nil =>
      intro hreflect hjoin
      simp [envJoinNames?] at hjoin
      cases hjoin
      exact hreflect
  | cons name names ih =>
      intro hreflect hjoin
      simp [envJoinNames?] at hjoin
      cases hstep : envJoinStep? left right result name with
      | none =>
          simp [hstep] at hjoin
      | some result' =>
          simp [hstep] at hjoin
          exact ih (entriesReflectLookup_envJoinStep? hreflect hstep) hjoin

private theorem entriesReflectLookup_envJoin? {left right out : FiniteEnv} :
    envJoin? left right = some out →
      EntriesReflectLookup out := by
  intro hjoin
  unfold envJoin? at hjoin
  exact entriesReflectLookup_envJoinNames? entriesReflectLookup_empty hjoin

private theorem entriesReflectLookup_envMove? {env moved : FiniteEnv}
    {lv : LVal} :
    EntriesReflectLookup env →
      envMove? env lv = some moved →
        EntriesReflectLookup moved := by
  intro hreflect hmove
  unfold envMove? at hmove
  cases hslot : env.lookup (LVal.base lv) with
  | none =>
      simp [hslot] at hmove
  | some slot =>
      cases hstrike : strike? (LVal.path lv) slot.ty with
      | none =>
          simp [hslot, hstrike] at hmove
      | some struck =>
          simp [hslot, hstrike] at hmove
          cases hmove
          exact entriesReflectLookup_update hreflect

mutual
  private theorem entriesReflectLookup_updateAtPath? :
      ∀ {fuel rank : Nat} {env : FiniteEnv} {path : Path}
        {oldTy : PartialTy} {rhsTy : Ty} {out : FiniteEnv}
        {updatedTy : PartialTy},
        EntriesReflectLookup env →
          updateAtPath? fuel rank env path oldTy rhsTy =
            some (out, updatedTy) →
            EntriesReflectLookup out := by
    intro fuel rank env path oldTy rhsTy out updatedTy hreflect h
    cases fuel with
    | zero =>
        simp [updateAtPath?] at h
    | succ fuel =>
        cases path with
        | nil =>
            cases rank with
            | zero =>
                simp [updateAtPath?] at h
                rcases h with ⟨rfl, rfl⟩
                exact hreflect
            | succ rank =>
                cases hshape :
                    shapeCompatiblePartialTy fuel env oldTy (.ty rhsTy) with
                | false =>
                    simp [updateAtPath?, hshape] at h
                | true =>
                    cases hjoin : partialTyJoin? oldTy (.ty rhsTy) with
                    | none =>
                        simp [updateAtPath?, hshape, hjoin] at h
                    | some joined =>
                        simp [updateAtPath?, hshape, hjoin] at h
                        rcases h with ⟨rfl, rfl⟩
                        exact hreflect
        | cons head rest =>
            cases head
            cases oldTy with
            | ty ty =>
                cases ty with
                | borrow mutable targets =>
                    cases mutable with
                    | false =>
                        simp [updateAtPath?] at h
                    | true =>
                        cases hwrite :
                            writeBorrowTargets? fuel (rank + 1) env rest targets
                              rhsTy with
                        | none =>
                            simp [updateAtPath?, hwrite] at h
                        | some writeEnv =>
                            simp [updateAtPath?, hwrite] at h
                            rcases h with ⟨rfl, rfl⟩
                            exact entriesReflectLookup_writeBorrowTargets?
                              hreflect hwrite
                | unit =>
                    simp [updateAtPath?] at h
                | int =>
                    simp [updateAtPath?] at h
                | box inner =>
                    simp [updateAtPath?] at h
                | bool =>
                    simp [updateAtPath?] at h
            | box inner =>
                cases hinner :
                    updateAtPath? fuel rank env rest inner rhsTy with
                | none =>
                    simp [updateAtPath?, hinner] at h
                | some result =>
                    rcases result with ⟨innerEnv, updatedInner⟩
                    simp [updateAtPath?, hinner] at h
                    rcases h with ⟨rfl, rfl⟩
                    exact entriesReflectLookup_updateAtPath? hreflect hinner
            | undef ty =>
                simp [updateAtPath?] at h
  termination_by fuel rank env path oldTy rhsTy out updatedTy hreflect h =>
    (fuel, 0, 0)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      first
      | omega
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))

  private theorem entriesReflectLookup_writeBorrowTargets? :
      ∀ {fuel rank : Nat} {env : FiniteEnv} {path : Path}
        {targets : List LVal} {rhsTy : Ty} {out : FiniteEnv},
        EntriesReflectLookup env →
          writeBorrowTargets? fuel rank env path targets rhsTy = some out →
            EntriesReflectLookup out := by
    intro fuel rank env path targets rhsTy out hreflect h
    cases targets with
    | nil =>
        simp [writeBorrowTargets?] at h
        cases h
        exact hreflect
    | cons target rest =>
        cases rest with
        | nil =>
            cases htype : lvalType? fuel env (prependPath path target) with
            | none =>
                simp [writeBorrowTargets?, htype] at h
            | some typed =>
                rcases typed with ⟨partialTy, leafLifetime⟩
                cases partialTy with
                | ty leafTy =>
                    cases hwrite :
                        envWrite? fuel rank env (prependPath path target)
                          rhsTy with
                    | none =>
                        simp [writeBorrowTargets?, htype, hwrite] at h
                    | some updated =>
                        simp [writeBorrowTargets?, htype, hwrite] at h
                        cases h
                        exact entriesReflectLookup_envWrite? hreflect hwrite
                | box inner =>
                    simp [writeBorrowTargets?, htype] at h
                | undef ty =>
                    simp [writeBorrowTargets?, htype] at h
        | cons restHead restTail =>
            cases htype : lvalType? fuel env (prependPath path target) with
            | none =>
                simp [writeBorrowTargets?, htype] at h
            | some typed =>
                rcases typed with ⟨partialTy, leafLifetime⟩
                cases partialTy with
                | ty leafTy =>
                    cases hwrite :
                        envWrite? fuel rank env (prependPath path target)
                          rhsTy with
                    | none =>
                        simp [writeBorrowTargets?, htype, hwrite] at h
                    | some updated =>
                        cases hrest :
                            writeBorrowTargets? fuel rank env path
                              (restHead :: restTail) rhsTy with
                        | none =>
                            simp [writeBorrowTargets?, htype, hwrite, hrest] at h
                        | some restUpdated =>
                            cases hjoin : envJoin? updated restUpdated with
                            | none =>
                                simp [writeBorrowTargets?, htype, hwrite, hrest,
                                  hjoin] at h
                            | some joined =>
                                simp [writeBorrowTargets?, htype, hwrite, hrest,
                                  hjoin] at h
                                cases h
                                exact entriesReflectLookup_envJoin? hjoin
                | box inner =>
                    simp [writeBorrowTargets?, htype] at h
                | undef ty =>
                    simp [writeBorrowTargets?, htype] at h
  termination_by fuel rank env path targets rhsTy out hreflect h =>
    (fuel, 2, targets.length)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      first
      | omega
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))

  private theorem entriesReflectLookup_envWrite? :
      ∀ {fuel rank : Nat} {env : FiniteEnv} {lv : LVal}
        {rhsTy : Ty} {out : FiniteEnv},
        EntriesReflectLookup env →
          envWrite? fuel rank env lv rhsTy = some out →
            EntriesReflectLookup out := by
    intro fuel rank env lv rhsTy out hreflect h
    unfold envWrite? at h
    cases hslot : env.lookup (LVal.base lv) with
    | none =>
        simp [hslot] at h
    | some slot =>
        cases hupdate :
            updateAtPath? fuel rank env (LVal.path lv) slot.ty rhsTy with
        | none =>
            simp [hslot, hupdate] at h
        | some result =>
            rcases result with ⟨writeEnv, updatedTy⟩
            simp [hslot, hupdate] at h
            cases h
            exact entriesReflectLookup_update
              (entriesReflectLookup_updateAtPath? hreflect hupdate)
  termination_by fuel rank env lv rhsTy out hreflect h => (fuel, 1, 0)
  decreasing_by
    all_goals
      simp_wf
      try subst_vars
      first
      | omega
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
      | exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))
end


private theorem envBorrowEdges_mem_exists_entry {entries : List (Name × EnvSlot)}
    {root : Name} {mutable : Bool} {targets : List LVal} :
    (root, mutable, targets) ∈
        entries.foldr
          (fun entry edges =>
            (partialTyBorrows entry.2.ty).map
                (fun borrow => (entry.1, borrow.1, borrow.2)) ++ edges)
          [] →
      ∃ slot,
        (root, slot) ∈ entries ∧
          (mutable, targets) ∈ partialTyBorrows slot.ty := by
  induction entries with
  | nil =>
      intro h
      simp at h
  | cons entry rest ih =>
      intro h
      rcases entry with ⟨entryName, entrySlot⟩
      change
        (root, mutable, targets) ∈
          (partialTyBorrows entrySlot.ty).map
              (fun borrow => (entryName, borrow.1, borrow.2)) ++
            rest.foldr
              (fun entry edges =>
                (partialTyBorrows entry.2.ty).map
                    (fun borrow => (entry.1, borrow.1, borrow.2)) ++ edges)
              [] at h
      rcases List.mem_append.mp h with hhead | hrest
      · rcases List.mem_map.mp hhead with ⟨borrow, hborrow, hedge⟩
        cases hedge
        exact ⟨entrySlot, List.mem_cons_self, hborrow⟩
      · rcases ih hrest with ⟨slot, hentry, hborrow⟩
        exact ⟨slot, List.mem_cons_of_mem _ hentry, hborrow⟩

private theorem envBorrowEdges_contains_sound {env : FiniteEnv}
    {root : Name} {mutable : Bool} {targets : List LVal} :
    EntriesReflectLookup env →
      (root, mutable, targets) ∈ envBorrowEdges env →
        env.toEnv ⊢ root ↝ Ty.borrow mutable targets := by
  intro hreflect hedge
  rcases envBorrowEdges_mem_exists_entry hedge with
    ⟨slot, hentry, hborrow⟩
  exact ⟨slot, hreflect hentry,
    partialTyContainsBorrow_of_mem hborrow⟩

private theorem rhsBorrowTargetsBelow_sound {envBefore result : FiniteEnv}
    {rhsTy : Ty} :
    rhsBorrowTargetsBelow envBefore result rhsTy = true →
      ∃ φ, LinearizedBy φ envBefore.toEnv ∧
        EnvWriteRhsBorrowTargetsBelow φ result.toEnv rhsTy := by
  intro h
  let fuel := (envNames envBefore).length + (envNames result).length + 1
  let φ : Name → Nat :=
    fun name => (rankOf? fuel result name).getD 0
  unfold rhsBorrowTargetsBelow at h
  change
    (linearizedByRanks? fuel result envBefore &&
      result.entries.all (fun entry =>
        (partialTyBorrows entry.2.ty).all (fun borrow =>
          borrow.2.all (fun target =>
            if targetInBorrowTargets target (tyBorrows rhsTy) then
              match rankOf? fuel result (LVal.base target),
                  rankOf? fuel result entry.1 with
              | some targetRank, some rootRank => targetRank < rootRank
              | _, _ => false
            else
              true))) &&
      (envBorrowEdges result).all (fun left =>
        (envBorrowEdges result).all (fun right =>
          left.2.2.all (fun leftTarget =>
            right.2.2.all (fun rightTarget =>
              if left.2.1 && pathConflicts leftTarget rightTarget &&
                  targetInBorrowTargets leftTarget (tyBorrows rhsTy) &&
                  targetInBorrowTargets rightTarget (tyBorrows rhsTy) then
                left.1 == right.1
              else
                true))))) = true at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hpreAndRank, hfanout⟩
  rcases Bool.and_eq_true_iff.mp hpreAndRank with ⟨hpre, hrank⟩
  refine ⟨φ, linearizedByRanks?_sound hpre, ?_⟩
  constructor
  · intro x slot mutable targets target hslot hcontains htarget hrhs
    change result.lookup x = some slot at hslot
    have hentry : (x, slot) ∈ result.entries :=
      lookupEntries_mem hslot
    have hborrowMem :
        (mutable, targets) ∈ partialTyBorrows slot.ty :=
      partialTyContainsBorrow_mem hcontains
    have hentryCheck :=
      (List.all_eq_true.mp hrank) (x, slot) hentry
    have hborrowCheck :=
      (List.all_eq_true.mp hentryCheck) (mutable, targets) hborrowMem
    have htargetCheck :=
      (List.all_eq_true.mp hborrowCheck) target htarget
    have htargetIn :
        targetInBorrowTargets target (tyBorrows rhsTy) = true :=
      targetInBorrowTargets_true hrhs
    simp [htargetIn] at htargetCheck
    cases htargetRank : rankOf? fuel result (LVal.base target) with
    | none =>
        simp [htargetRank] at htargetCheck
    | some targetRank =>
        cases hrootRank : rankOf? fuel result x with
        | none =>
            simp [htargetRank, hrootRank] at htargetCheck
        | some rootRank =>
            simp [htargetRank, hrootRank] at htargetCheck
            simpa [φ, htargetRank, hrootRank] using htargetCheck
  · intro x y mutable targetsMutable targetsOther targetMutable targetOther
      hleftContains hrightContains htargetMutable htargetOther hconflict
      hrhsMutable hrhsOther
    have hleftEdge :
        (x, true, targetsMutable) ∈ envBorrowEdges result :=
      envBorrowEdges_of_contains hleftContains
    have hrightEdge :
        (y, mutable, targetsOther) ∈ envBorrowEdges result :=
      envBorrowEdges_of_contains hrightContains
    have hleftCheck :=
      (List.all_eq_true.mp hfanout) (x, true, targetsMutable) hleftEdge
    have hrightCheck :=
      (List.all_eq_true.mp hleftCheck) (y, mutable, targetsOther) hrightEdge
    have htargetMutableCheck :=
      (List.all_eq_true.mp hrightCheck) targetMutable htargetMutable
    have htargetOtherCheck :=
      (List.all_eq_true.mp htargetMutableCheck) targetOther htargetOther
    have hconflictBool :
        pathConflicts targetMutable targetOther = true := by
      simpa [pathConflicts, PathConflicts] using hconflict
    have htargetMutableIn :
        targetInBorrowTargets targetMutable (tyBorrows rhsTy) = true :=
      targetInBorrowTargets_true hrhsMutable
    have htargetOtherIn :
        targetInBorrowTargets targetOther (tyBorrows rhsTy) = true :=
      targetInBorrowTargets_true hrhsOther
    simp [hconflictBool, htargetMutableIn, htargetOtherIn] at htargetOtherCheck
    simpa using htargetOtherCheck

private theorem tyBorrowSafeAgainstEnv_sound {env : FiniteEnv} {ty : Ty} :
    tyBorrowSafeAgainstEnv env ty = true →
      TyBorrowSafeAgainstEnv env.toEnv ty := by
  intro h
  unfold tyBorrowSafeAgainstEnv at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hleftSafe, hrightSafe⟩
  constructor
  · intro targetsMutable mutable targetsOther x targetMutable targetOther
      htyContains henvContains htargetMutable htargetOther hconflict
    have htyMem :
        (true, targetsMutable) ∈ tyBorrows ty :=
      partialTyContainsBorrow_mem
        (partialTy := .ty ty) htyContains
    have hedge :
        (x, mutable, targetsOther) ∈ envBorrowEdges env :=
      envBorrowEdges_of_contains henvContains
    have htyCheck :=
      (List.all_eq_true.mp hleftSafe) (true, targetsMutable) htyMem
    simp at htyCheck
    have htargetOtherCheck :
        pathConflicts targetMutable targetOther = false := by
      cases mutable
      · exact (htyCheck x).1 targetsOther hedge
          targetMutable htargetMutable targetOther htargetOther
      · exact (htyCheck x).2 targetsOther hedge
          targetMutable htargetMutable targetOther htargetOther
    have hconflictBool : pathConflicts targetMutable targetOther = true := by
      simpa [pathConflicts, PathConflicts] using hconflict
    rw [hconflictBool] at htargetOtherCheck
    simp at htargetOtherCheck
  · intro x targetsMutable mutable targetsOther targetMutable targetOther
      henvContains htyContains htargetMutable htargetOther hconflict
    have hedge :
        (x, true, targetsMutable) ∈ envBorrowEdges env :=
      envBorrowEdges_of_contains henvContains
    have htyMem :
        (mutable, targetsOther) ∈ tyBorrows ty :=
      partialTyContainsBorrow_mem
        (partialTy := .ty ty) htyContains
    have hedgeCheck :=
      (List.all_eq_true.mp hrightSafe) (x, true, targetsMutable) hedge
    simp at hedgeCheck
    have htargetOtherCheck :
        pathConflicts targetMutable targetOther = false := by
      cases mutable
      · exact hedgeCheck.1 targetsOther htyMem
          targetMutable htargetMutable targetOther htargetOther
      · exact hedgeCheck.2 targetsOther htyMem
          targetMutable htargetMutable targetOther htargetOther
    have hconflictBool : pathConflicts targetMutable targetOther = true := by
      simpa [pathConflicts, PathConflicts] using hconflict
    rw [hconflictBool] at htargetOtherCheck
    simp at htargetOtherCheck

private theorem borrowSafeRoot_sound {env : FiniteEnv} {root : Name} :
    borrowSafeRoot env root = true → BorrowSafeRoot env.toEnv root := by
  intro h y mutable targetsMutable targetsOther targetMutable targetOther
    hrootContains hotherContains htargetMutable htargetOther hconflict
  unfold borrowSafeRoot at h
  have hrootEdge :
      (root, true, targetsMutable) ∈ envBorrowEdges env :=
    envBorrowEdges_of_contains hrootContains
  have hrootFiltered :
      (root, true, targetsMutable) ∈
        (envBorrowEdges env).filter
          (fun edge => edge.1 == root && edge.2.1) := by
    apply List.mem_filter.mpr
    constructor
    · exact hrootEdge
    · simp
  have hotherEdge :
      (y, mutable, targetsOther) ∈ envBorrowEdges env :=
    envBorrowEdges_of_contains hotherContains
  have hrootCheck :=
    (List.all_eq_true.mp h) (root, true, targetsMutable) hrootFiltered
  have hotherCheck :=
    (List.all_eq_true.mp hrootCheck) (y, mutable, targetsOther) hotherEdge
  have htargetMutableCheck :=
    (List.all_eq_true.mp hotherCheck) targetMutable htargetMutable
  have htargetOtherCheck :=
    (List.all_eq_true.mp htargetMutableCheck) targetOther htargetOther
  have hconflictBool : pathConflicts targetMutable targetOther = true := by
    simpa [pathConflicts, PathConflicts] using hconflict
  simp [hconflictBool] at htargetOtherCheck
  simpa using htargetOtherCheck

private theorem readProhibited_false_sound {env : FiniteEnv} {lv : LVal} :
    readProhibited env lv = false →
      ¬ ReadProhibited env.toEnv lv := by
  intro hfalse hread
  rcases hread with ⟨root, targets, target, hcontains, htarget, hconflict⟩
  have hedge :
      (root, true, targets) ∈ envBorrowEdges env :=
    envBorrowEdges_of_contains hcontains
  have htargetConflict : pathConflicts target lv = true := by
    simpa [pathConflicts, PathConflicts] using hconflict
  have hany : readProhibited env lv = true := by
    rw [readProhibited, List.any_eq_true]
    refine ⟨(root, true, targets), hedge, ?_⟩
    simp [List.any_eq_true]
    exact ⟨target, htarget, htargetConflict⟩
  rw [hfalse] at hany
  cases hany

private theorem readProhibited_true_sound {env : FiniteEnv} {lv : LVal} :
    EntriesReflectLookup env →
      readProhibited env lv = true →
        ReadProhibited env.toEnv lv := by
  intro hreflect htrue
  rw [readProhibited, List.any_eq_true] at htrue
  rcases htrue with ⟨edge, hedge, hconflictInEdge⟩
  rcases edge with ⟨root, mutable, targets⟩
  rcases Bool.and_eq_true_iff.mp hconflictInEdge with
    ⟨hmutable, htargets⟩
  have hmutableEq : mutable = true := by
    simpa using hmutable
  subst mutable
  rcases List.any_eq_true.mp htargets with
    ⟨target, htarget, hconflict⟩
  exact ⟨root, targets, target,
    envBorrowEdges_contains_sound hreflect hedge, htarget,
    by simpa [pathConflicts, PathConflicts] using hconflict⟩

private theorem readProhibited_complete {env : FiniteEnv} {lv : LVal} :
    EntriesReflectLookup env →
      ¬ ReadProhibited env.toEnv lv →
        readProhibited env lv = false := by
  intro hreflect hnot
  cases hread : readProhibited env lv
  · rfl
  · exact False.elim (hnot (readProhibited_true_sound hreflect hread))

private theorem writeProhibited_false_sound {env : FiniteEnv} {lv : LVal} :
    writeProhibited env lv = false →
      ¬ WriteProhibited env.toEnv lv := by
  intro hfalse hwrite
  simp [writeProhibited] at hfalse
  rcases hfalse with ⟨hreadFalse, himmFalse⟩
  cases hwrite with
  | inl hread =>
      exact readProhibited_false_sound hreadFalse hread
  | inr himm =>
      rcases himm with
        ⟨root, targets, target, hcontains, htarget, hconflict⟩
      have hedge :
          (root, false, targets) ∈ envBorrowEdges env :=
        envBorrowEdges_of_contains hcontains
      have htargetConflict : pathConflicts target lv = true := by
        simpa [pathConflicts, PathConflicts] using hconflict
      have htargetFalse :=
        (himmFalse root).1 targets hedge target htarget
      rw [htargetConflict] at htargetFalse
      cases htargetFalse

private theorem writeProhibited_true_sound {env : FiniteEnv} {lv : LVal} :
    EntriesReflectLookup env →
      writeProhibited env lv = true →
        WriteProhibited env.toEnv lv := by
  intro hreflect htrue
  unfold writeProhibited at htrue
  cases hread : readProhibited env lv
  · have hany :
        (envBorrowEdges env).any (fun edge =>
          edge.2.2.any (fun target => pathConflicts target lv)) = true := by
      simpa [hread] using htrue
    rw [List.any_eq_true] at hany
    rcases hany with ⟨edge, hedge, htargetInEdge⟩
    rcases edge with ⟨root, mutable, targets⟩
    rcases List.any_eq_true.mp htargetInEdge with
      ⟨target, htarget, hconflict⟩
    have hcontains :
        env.toEnv ⊢ root ↝ Ty.borrow mutable targets :=
      envBorrowEdges_contains_sound hreflect hedge
    cases mutable
    · exact Or.inr ⟨root, targets, target, hcontains, htarget,
        by simpa [pathConflicts, PathConflicts] using hconflict⟩
    · exact Or.inl ⟨root, targets, target, hcontains, htarget,
        by simpa [pathConflicts, PathConflicts] using hconflict⟩
  · exact Or.inl (readProhibited_true_sound hreflect hread)

private theorem writeProhibited_complete {env : FiniteEnv} {lv : LVal} :
    EntriesReflectLookup env →
      ¬ WriteProhibited env.toEnv lv →
        writeProhibited env lv = false := by
  intro hreflect hnot
  cases hwrite : writeProhibited env lv
  · rfl
  · exact False.elim (hnot (writeProhibited_true_sound hreflect hwrite))

private theorem checker_not_pathConflicts_of_not_writeProhibited_contains
    {env : Env} {lv target : LVal} {x : Name}
    {mutable : Bool} {targets : List LVal} :
    ¬ WriteProhibited env lv →
    env ⊢ x ↝ Ty.borrow mutable targets →
    target ∈ targets →
      ¬ target ⋈ lv := by
  intro hnotWrite hcontains htarget hconflict
  cases mutable with
  | false =>
      exact hnotWrite
        (Or.inr ⟨x, targets, target, hcontains, htarget, hconflict⟩)
  | true =>
      exact hnotWrite
        (Or.inl ⟨x, targets, target, hcontains, htarget, hconflict⟩)

private theorem lvalTyping_no_writeProhibited_targets {env : Env}
    {written : LVal} :
    ¬ WriteProhibited env written →
    (∀ {lv partialTy lifetime},
      LValTyping env lv partialTy lifetime →
      ∀ {mutable targets},
        PartialTyContains partialTy (.borrow mutable targets) →
        ∀ target,
          target ∈ targets →
          ¬ target ⋈ written) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping env targets partialTy lifetime →
      ∀ {mutable borrowTargets},
        PartialTyContains partialTy (.borrow mutable borrowTargets) →
        ∀ target,
          target ∈ borrowTargets →
          ¬ target ⋈ written) := by
  intro hnotWrite
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun _lv partialTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ written)
      (motive_2 := fun _targetLvs unionTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains unionTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ written)
      (by
        intro x slot hslot mutable targets hcontains target htarget
        exact checker_not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          ⟨slot, hslot, hcontains⟩ htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains
          target htarget
        exact ih (PartialTyContains.box hcontains) target htarget)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets mutable targets hcontains
          target htarget
        exact ihTargets hcontains target htarget)
      (by
        intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
          hcontains target htarget
        exact ihTarget hcontains target htarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
          _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
          _mutable _targets hcontains selected hselected
        rcases PartialTyUnion.contained_borrow_member hunion hcontains
            hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with
            ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead
        · rcases hselectedRest with
            ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun _lv partialTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains partialTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ written)
      (motive_2 := fun _targetLvs unionTy _ _ =>
        ∀ {mutable targets},
          PartialTyContains unionTy (.borrow mutable targets) →
          ∀ target,
            target ∈ targets →
            ¬ target ⋈ written)
      (by
        intro x slot hslot mutable targets hcontains target htarget
        exact checker_not_pathConflicts_of_not_writeProhibited_contains hnotWrite
          ⟨slot, hslot, hcontains⟩ htarget)
      (by
        intro _lv _inner _lifetime _htyping ih mutable targets hcontains
          target htarget
        exact ih (PartialTyContains.box hcontains) target htarget)
      (by
        intro _lv _mutable _targets _borrowLifetime _targetLifetime _targetTy
          _hborrow _htargets _ihBorrow ihTargets mutable targets hcontains
          target htarget
        exact ihTargets hcontains target htarget)
      (by
        intro _target _ty _targetLifetime _htarget ihTarget _mutable _targets
          hcontains target htarget
        exact ihTarget hcontains target htarget)
      (by
        intro _target _rest _headTy _headLifetime _restLifetime _targetLifetime
          _restTy _unionTy _hhead _hrest hunion _hintersection ihHead ihRest
          _mutable _targets hcontains selected hselected
        rcases PartialTyUnion.contained_borrow_member hunion hcontains
            hselected with
          hselectedHead | hselectedRest
        · rcases hselectedHead with
            ⟨headTargets, hheadContains, hselectedHead⟩
          exact ihHead hheadContains selected hselectedHead
        · rcases hselectedRest with
            ⟨restTargets, hrestContains, hselectedRest⟩
          exact ihRest hrestContains selected hselectedRest)
      htyping

private theorem lvalTyping_transport_of_lookup_eq_notWrite
    {source target : FiniteEnv} {written : LVal}
    (hlookup :
      ∀ name, name ≠ LVal.base written →
        source.lookup name = target.lookup name)
    (hnotWrite : ¬ WriteProhibited source.toEnv written) :
    (∀ {lv partialTy lifetime},
      LValTyping source.toEnv lv partialTy lifetime →
      ¬ lv ⋈ written →
        LValTyping target.toEnv lv partialTy lifetime) ∧
    (∀ {targets partialTy lifetime},
      LValTargetsTyping source.toEnv targets partialTy lifetime →
      (∀ target, target ∈ targets → ¬ target ⋈ written) →
        LValTargetsTyping target.toEnv targets partialTy lifetime) := by
  constructor
  · intro lv partialTy lifetime htyping
    exact LValTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ written →
          LValTyping target.toEnv lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ written) →
          LValTargetsTyping target.toEnv targets partialTy lifetime)
      (by
        intro x slot hslot hnotConflict
        have hx : x ≠ LVal.base written := by
          intro hx
          exact hnotConflict hx
        exact LValTyping.var (by
          simpa [FiniteEnv.toEnv, hlookup x hx] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ written := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ written := by
          intro target htarget
          exact (lvalTyping_no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow (ihBorrow hnotBorrow)
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping
  · intro targets partialTy lifetime htyping
    exact LValTargetsTyping.rec
      (motive_1 := fun lv partialTy lifetime _ =>
        ¬ lv ⋈ written →
          LValTyping target.toEnv lv partialTy lifetime)
      (motive_2 := fun targets partialTy lifetime _ =>
        (∀ target, target ∈ targets → ¬ target ⋈ written) →
          LValTargetsTyping target.toEnv targets partialTy lifetime)
      (by
        intro x slot hslot hnotConflict
        have hx : x ≠ LVal.base written := by
          intro hx
          exact hnotConflict hx
        exact LValTyping.var (by
          simpa [FiniteEnv.toEnv, hlookup x hx] using hslot))
      (by
        intro lv inner lifetime _htyping ih hnotConflict
        exact LValTyping.box
          (ih (by simpa [PathConflicts, LVal.base] using hnotConflict)))
      (by
        intro lv mutable targets borrowLifetime targetLifetime targetTy
          hborrow _htargets ihBorrow ihTargets hnotConflict
        have hnotBorrow : ¬ lv ⋈ written := by
          simpa [PathConflicts, LVal.base] using hnotConflict
        have htargetsNoConflict :
            ∀ target, target ∈ targets → ¬ target ⋈ written := by
          intro target htarget
          exact (lvalTyping_no_writeProhibited_targets hnotWrite).1
            hborrow PartialTyContains.here target htarget
        exact LValTyping.borrow (ihBorrow hnotBorrow)
          (ihTargets htargetsNoConflict))
      (by
        intro target ty lifetime _htarget ihTarget hnotTargets
        exact LValTargetsTyping.singleton
          (ihTarget (hnotTargets target (by simp))))
      (by
        intro target rest headTy headLifetime restLifetime lifetime restTy unionTy
          _hhead _hrest hunion hintersection ihHead ihRest hnotTargets
        exact LValTargetsTyping.cons
          (ihHead (hnotTargets target (by simp)))
          (ihRest (by
            intro selected hselected
            exact hnotTargets selected (by simp [hselected])))
          hunion hintersection)
      htyping

private theorem envWriteCoherenceObligations_of_checker {fuel : Nat}
    {before result : FiniteEnv} {lhs : LVal} :
    envEqOutside before result (LVal.base lhs) = true →
    coherentNonempty fuel result = true →
    rootCoherent fuel result (LVal.base lhs) = true →
    Linearizable result.toEnv →
    ¬ WriteProhibited result.toEnv lhs →
      EnvWriteCoherenceObligations before.toEnv result.toEnv (LVal.base lhs) := by
  intro houtside hcoherentNonempty hrootCoherent hlinear hnotWrite
  constructor
  · intro lv mutable targets borrowLifetime hbase htyping
    have hlookup :
        ∀ name, name ≠ LVal.base lhs →
          result.lookup name = before.lookup name := by
      intro name hne
      exact (envEqOutside_lookup_eq houtside name hne).symm
    have hnotConflict : ¬ lv ⋈ lhs := by
      intro hconflict
      exact hbase hconflict
    have htypingBefore :
        LValTyping before.toEnv lv (.ty (.borrow mutable targets))
          borrowLifetime :=
      (lvalTyping_transport_of_lookup_eq_notWrite
          (source := result) (target := before) (written := lhs)
          hlookup hnotWrite).1 htyping hnotConflict
    refine ⟨⟨borrowLifetime, htypingBefore⟩, ?_⟩
    intro targetTy targetLifetime htargetsBefore
    have htargetsNonempty : targets ≠ [] := by
      intro hnil
      subst hnil
      exact LValTargetsTyping.nil_false htargetsBefore
    exact coherentNonempty_lvalTyping_sound
      hcoherentNonempty hlinear htyping htargetsNonempty
  · intro lv mutable targets borrowLifetime hbase htyping
    exact rootCoherent_written_root_sound
      hrootCoherent hlinear hbase htyping

private theorem writeProhibited_update_fresh_false_of_contained
    {env : Env} {name : Name} {ty : Ty} {lifetime : Lifetime} :
    ContainedBorrowsWellFormed env →
    WellFormedTy env ty lifetime →
    env.fresh name →
      ¬ WriteProhibited
        (env.update name { ty := .ty ty, lifetime := lifetime }) (.var name) := by
  intro hcontained hwellTy hfresh hwrite
  have htargetFresh :
      ∀ {root slot mutable targets target},
        (env.update name { ty := .ty ty, lifetime := lifetime }).slotAt root =
          some slot →
        PartialTyContains slot.ty (.borrow mutable targets) →
        target ∈ targets →
          LVal.base target ≠ name := by
    intro root slot mutable targets target hslot hcontains htarget hbase
    by_cases hroot : root = name
    · subst hroot
      have hslotEq :
          slot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
        have h :
            { ty := PartialTy.ty ty, lifetime := lifetime } = slot := by
          simpa [Env.update] using hslot
        exact h.symm
      subst hslotEq
      have htargets :=
        borrowTargetsWellFormedInSlot_of_wellFormedTy_contains
          hwellTy hcontains target htarget
      rcases htargets with ⟨targetTy, targetLifetime, htyping, _houtlives, _hbase⟩
      rcases LValTyping.base_slot_exists htyping with ⟨targetSlot, htargetSlot⟩
      rw [hbase, hfresh] at htargetSlot
      cases htargetSlot
    · have hslotOld : env.slotAt root = some slot := by
        simpa [Env.update, hroot] using hslot
      have hcontainsOld :
          env ⊢ root ↝ Ty.borrow mutable targets :=
        ⟨slot, hslotOld, hcontains⟩
      have htargets :=
        hcontained root slot mutable targets hslotOld hcontainsOld target
          htarget
      rcases htargets with ⟨targetTy, targetLifetime, htyping, _houtlives, _hbase⟩
      rcases LValTyping.base_slot_exists htyping with ⟨targetSlot, htargetSlot⟩
      rw [hbase, hfresh] at htargetSlot
      cases htargetSlot
  cases hwrite with
  | inl hread =>
      rcases hread with ⟨root, targets, target, hcontains, htarget, hconflict⟩
      rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
      have hbase : LVal.base target = name := by
        simpa [PathConflicts, LVal.base] using hconflict
      exact (htargetFresh hslot hcontainsTy htarget) hbase
  | inr himm =>
      rcases himm with ⟨root, targets, target, hcontains, htarget, hconflict⟩
      rcases hcontains with ⟨slot, hslot, hcontainsTy⟩
      have hbase : LVal.base target = name := by
        simpa [PathConflicts, LVal.base] using hconflict
      exact (htargetFresh hslot hcontainsTy htarget) hbase

private theorem freshUpdateCoherenceObligations_of_checker {fuel : Nat}
    {env updated : FiniteEnv} {name : Name} {ty : Ty}
    {lifetime : Lifetime} :
    updated = env.update name { ty := .ty ty, lifetime := lifetime } →
    ContainedBorrowsWellFormed env.toEnv →
    WellFormedTy env.toEnv ty lifetime →
    env.toEnv.fresh name →
    wellFormedKit fuel updated = true →
      FreshUpdateCoherenceObligations env.toEnv name ty lifetime := by
  intro hupdated hcontained hwellTy hfresh hkit
  subst hupdated
  let slot : EnvSlot := { ty := .ty ty, lifetime := lifetime }
  have hnotWrite :
      ¬ WriteProhibited (env.update name slot).toEnv (.var name) := by
    simpa [slot, FiniteEnv.toEnv_update] using
      writeProhibited_update_fresh_false_of_contained
        hcontained hwellTy hfresh
  constructor
  · intro lv mutable targets borrowLifetime hbase htyping
    have hlookup :
        ∀ root, root ≠ name →
          (env.update name slot).lookup root = env.lookup root := by
      intro root hne
      exact lookup_update_ne env slot hne
    have hnotConflict : ¬ lv ⋈ (.var name) := by
      intro hconflict
      exact hbase hconflict
    have htypingUpdated :
        LValTyping (env.update name slot).toEnv lv
          (.ty (.borrow mutable targets)) borrowLifetime := by
      simpa [slot, FiniteEnv.toEnv_update] using htyping
    exact ⟨borrowLifetime,
      (lvalTyping_transport_of_lookup_eq_notWrite
          (source := env.update name slot) (target := env)
          (written := .var name) hlookup hnotWrite).1
        htypingUpdated hnotConflict⟩
  · intro lv mutable targets borrowLifetime hbase htyping
    have hcoherent : Coherent (env.update name slot).toEnv :=
      wellFormedKit_coherent_sound hkit
    have htypingUpdated :
        LValTyping (env.update name slot).toEnv lv
          (.ty (.borrow mutable targets)) borrowLifetime := by
      simpa [slot, FiniteEnv.toEnv_update] using htyping
    rcases hcoherent lv mutable targets borrowLifetime htypingUpdated with
      ⟨targetTy, targetLifetime, htargets⟩
    exact ⟨targetTy, targetLifetime, by
      simpa [slot, FiniteEnv.toEnv_update] using htargets⟩

private theorem envSlotsOutlive_update_fresh_current
    {env : Env} {name : Name} {ty : Ty} {lifetime : Lifetime} :
    EnvSlotsOutlive env lifetime →
    env.fresh name →
      EnvSlotsOutlive
        (env.update name { ty := .ty ty, lifetime := lifetime }) lifetime := by
  intro houtlives hfresh candidate slot hslot
  by_cases hname : candidate = name
  · subst candidate
    have hslotEq :
        slot = { ty := PartialTy.ty ty, lifetime := lifetime } := by
      exact (Option.some.inj (by simpa [Env.update] using hslot)).symm
    subst hslotEq
    exact LifetimeOutlives.refl lifetime
  · have hold : env.slotAt candidate = some slot := by
      simpa [Env.update, hname] using hslot
    exact houtlives candidate slot hold

private def CheckerStoreTypingRefsWellFormed
    (env : Env) (typing : StoreTyping) (lifetime : Lifetime) : Prop :=
  ∀ (ref : Reference) (ty : Ty),
    typing.tyOf ref.location = some ty →
    WellFormedTy env ty lifetime

private def CheckTermSoundAt (fuel : Nat) : Prop :=
  ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {result : CheckResult},
    (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
    WellFormedEnv env.toEnv lifetime →
    checkTerm? fuel env typing lifetime term = .ok result →
      TermTyping env.toEnv typing lifetime term result.ty result.env.toEnv ∧
        WellFormedEnv result.env.toEnv lifetime ∧
          WellFormedTy result.env.toEnv result.ty lifetime

private theorem valueTyping_result_wellFormed_of_checkerRefs {env : Env}
    {typing : StoreTyping} {lifetime : Lifetime} {value : Value} {ty : Ty} :
    CheckerStoreTypingRefsWellFormed env typing lifetime →
    ValueTyping typing value ty →
    WellFormedTy env ty lifetime := by
  intro hrefs htyping
  cases htyping with
  | unit | int | bool => constructor
  | ref hlookup =>
      exact hrefs _ _ hlookup

private theorem checkTermList?_sound_of_termSound {fuel : Nat}
    (termSound : CheckTermSoundAt fuel) :
    ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
      {terms : List Term} {result : CheckResult},
      (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
      checkTermList? fuel env typing lifetime terms = .ok result →
        TermListTyping env.toEnv typing lifetime terms result.ty result.env.toEnv ∧
          WellFormedEnv result.env.toEnv lifetime ∧
            WellFormedTy result.env.toEnv result.ty lifetime := by
  intro env typing lifetime terms
  induction terms generalizing env with
  | nil =>
      intro result hrefs hwell hcheck
      simp [checkTermList?] at hcheck
  | cons term rest ih =>
      intro result hrefs hwell hcheck
      cases rest with
      | nil =>
          simp [checkTermList?] at hcheck
          have hterm := termSound hrefs hwell hcheck
          exact ⟨TermListTyping.singleton hterm.1, hterm.2⟩
      | cons restHead restTail =>
          cases hhead : checkTerm? fuel env typing lifetime term with
          | error message =>
              simp [checkTermList?, hhead, Bind.bind, Except.bind] at hcheck
          | ok headResult =>
              simp [checkTermList?, hhead, Except.bind] at hcheck
              have hheadSound := termSound hrefs hwell hhead
              have hrestSound := ih hrefs hheadSound.2.1 hcheck
              exact ⟨TermListTyping.cons hheadSound.1 hrestSound.1,
                hrestSound.2⟩

private def CheckTermTypingSoundAt (fuel : Nat) : Prop :=
  ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {result : CheckResult},
    checkTerm? fuel env typing lifetime term = .ok result →
      TermTyping env.toEnv typing lifetime term result.ty result.env.toEnv

private theorem checkTermList?_typing_sound_of_termSound {fuel : Nat}
    (termSound : CheckTermTypingSoundAt fuel) :
    ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
      {terms : List Term} {result : CheckResult},
      checkTermList? fuel env typing lifetime terms = .ok result →
        TermListTyping env.toEnv typing lifetime terms result.ty
          result.env.toEnv := by
  intro env typing lifetime terms
  induction terms generalizing env with
  | nil =>
      intro result hcheck
      simp [checkTermList?] at hcheck
  | cons term rest ih =>
      intro result hcheck
      cases rest with
      | nil =>
          simp [checkTermList?] at hcheck
          exact TermListTyping.singleton (termSound hcheck)
      | cons restHead restTail =>
          cases hhead : checkTerm? fuel env typing lifetime term with
          | error message =>
              simp [checkTermList?, hhead, Bind.bind, Except.bind] at hcheck
          | ok headResult =>
              simp [checkTermList?, hhead, Except.bind] at hcheck
              exact TermListTyping.cons (termSound hhead) (ih hcheck)

private theorem termTyping_preserves_wellFormed_for_checker
    {env₁ env₂ : Env} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {ty : Ty} :
    (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
    WellFormedEnv env₁ lifetime →
    TermTyping env₁ typing lifetime term ty env₂ →
      WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime := by
  intro hrefs hwell htyping
  exact TermTyping.rec
    (motive_1 := fun env currentTyping lifetime term ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
        WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (motive_2 := fun env currentTyping lifetime terms ty env₂ _ =>
      currentTyping = typing →
      WellFormedEnv env lifetime →
        WellFormedEnv env₂ lifetime ∧ WellFormedTy env₂ ty lifetime)
    (fun {_env _typing _lifetime _value _ty} hvalueTyping htypingEq
        hwellFormed =>
      by
        subst htypingEq
        exact ⟨hwellFormed,
          valueTyping_result_wellFormed_of_checkerRefs
            (hrefs _ _) hvalueTyping⟩)
    (fun {_env _typing _lifetime _ty} hwellTy _hloanFree _htypingEq
        hwellFormed =>
      ⟨hwellFormed, hwellTy⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty} hLv hcopy _hread
        _htypingEq hwellFormed =>
      ⟨hwellFormed, copyTy_result_wellFormed hwellFormed hLv hcopy⟩)
    (fun {_env₁ _env₂ _typing _lifetime _valueLifetime _lv _ty}
        hLv hnotWrite hmove _htypingEq hwellFormed =>
      move_preserves_wellFormed hwellFormed hLv hnotWrite hmove)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty}
        hLv _hmutable _hwrite _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env _typing _lifetime _valueLifetime _lv _ty}
        hLv _hread _htypingEq hwellFormed =>
      ⟨hwellFormed,
        WellFormedTy.borrow
          (BorrowTargetsWellFormed.singleton hLv
            (LValTyping.lifetime_outlives_one hwellFormed hLv)
            (LValTyping.base_outlives_one hwellFormed hLv))⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      let result := ih htypingEq hwellFormed
      ⟨result.1, WellFormedTy.box result.2⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _blockLifetime _terms _ty}
        hblockChild hterms hwellTy hdrop ih htypingEq hwellFormed =>
      let bodyResult :=
        ih htypingEq
          (WellFormedEnv.weaken hwellFormed
            (LifetimeChild.outlives hblockChild))
      block_preserves_wellFormed hblockChild bodyResult.1 hterms hwellTy
        hdrop)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _x _term _ty}
        _hfresh _hterm hfreshOut hcohObligations henv₃ ih htypingEq
        hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        refine ⟨?_, WellFormedTy.unit⟩
        rw [henv₃]
        exact WellFormedEnv.update_fresh_ty_of_coherenceObligations
          result.1 result.2 hfreshOut hcohObligations)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _targetLifetime _lhs _oldTy
          _rhs _rhsTy}
        hLhs hRhs _hLhsPost _hshape _hwellRhs hwrite hranked
        hwriteCoh hcontained hnotWrite ih htypingEq hwellFormed =>
      by
        let result := ih htypingEq hwellFormed
        rcases hranked with ⟨φ, hlinBy, hbelow⟩
        have hlin3By :=
          EnvWrite.preserves_linearizedBy_of_rhsBorrowTargetsBelow_all
            hwrite hlinBy hbelow
        have hcoh3 := EnvWrite.preserves_coherent_of_obligations
          result.1.2.2.1 hwriteCoh
        exact ⟨⟨hcontained,
            EnvWrite.preserves_slotsOutlive result.1.2.1 hwrite,
            hcoh3,
            Linearizable.of_linearizedBy hlin3By⟩,
          WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _env₃ _envGhost _ghost _typing _lifetime _lhs _rhs
          _lhsTy _rhsTy _ghostRhsTy}
        _hLhs _hfresh _hghostRhs _hRhs _hcopyL _hcopyR _hshape
        ihL _ihGhost ihR htypingEq hwellFormed =>
      let leftResult := ihL htypingEq hwellFormed
      let rightResult := ihR htypingEq leftResult.1
      ⟨rightResult.1, WellFormedTy.bool⟩)
    (fun {_env₁ _env₂ _env₃ _env₄ _env₅ _typing _lifetime _condition
          _trueBranch _falseBranch _trueTy _falseTy _joinTy}
        _hcondition _htrue _hfalse _hjoin henvJoin _hsameLeft _hsameRight
        hwellJoin hcontained hcoherent hlinear ihCondition
        ihTrue _ihFalse htypingEq hwellFormed =>
      let conditionResult := ihCondition htypingEq hwellFormed
      let thenResult := ihTrue htypingEq conditionResult.1
      ⟨⟨hcontained,
          EnvSlotsOutlive.of_lifetimesPreserved thenResult.1.2.1
            (EnvJoin.lifetimesPreserved_left henvJoin),
          hcoherent, hlinear⟩,
        hwellJoin⟩)
    (fun {_env₁ _env₂ _env₃ _env₄ _typing _lifetime _condition
          _trueBranch _falseBranch _trueTy _falseTy}
        _hcondition _htrue _hfalse _hdiverges ihCondition ihTrue _ihFalse
        htypingEq hwellFormed =>
      let conditionResult := ihCondition htypingEq hwellFormed
      ihTrue htypingEq conditionResult.1)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _bodyLifetime _condition
          _body _bodyTy}
        _hchild _hcond _hbody _hwellTy _hdrop ihCond _ihBody htypingEq
        hwellFormed =>
      let conditionResult := ihCond htypingEq hwellFormed
      ⟨conditionResult.1, WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _bodyLifetime _condition
          _body _bodyTy}
        _hchild _hcond _hbody _hdiverges ihCond _ihBody htypingEq
        hwellFormed =>
      let conditionResult := ihCond htypingEq hwellFormed
      ⟨conditionResult.1, WellFormedTy.unit⟩)
    (fun {_env₁ _envBack _envInv _env₂ _envEntry₂ _env₃ _envEntry₃ _typing
          _lifetime _bodyLifetime _condition _body _bodyTy _bodyEntryTy}
        _hchild hjoin _hss1 _hss2 hcbwf hcoh hlin _hcondInv _hbodyInv
        _hwellTy _hdrop _hcondEntry _hbodyEntry ihCondInv _ihBodyInv
        _ihCondEntry _ihBodyEntry htypingEq hwellFormed =>
      let invWellFormed : WellFormedEnv _envInv _lifetime :=
        ⟨hcbwf,
          EnvSlotsOutlive.of_lifetimesPreserved hwellFormed.2.1
            (EnvJoin.lifetimesPreserved_left hjoin),
          hcoh, hlin⟩
      let conditionResult := ihCondInv htypingEq invWellFormed
      ⟨conditionResult.1, WellFormedTy.unit⟩)
    (fun {_env₁ _env₂ _typing _lifetime _term _ty} _hterm ih htypingEq
        hwellFormed =>
      ih htypingEq hwellFormed)
    (fun {_env₁ _env₂ _env₃ _typing _lifetime _term _rest _termTy _finalTy}
        _hterm _hrest ihHead ihRest htypingEq hwellFormed =>
      let headResult := ihHead htypingEq hwellFormed
      ihRest htypingEq headResult.1)
    htyping rfl hwell

private theorem checkTermSound_of_typing
    {env resultEnv : FiniteEnv} {typing : StoreTyping}
    {lifetime : Lifetime} {term : Term} {ty : Ty}
    (hrefs :
      ∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime)
    (hwell : WellFormedEnv env.toEnv lifetime)
    (htyping : TermTyping env.toEnv typing lifetime term ty resultEnv.toEnv) :
    TermTyping env.toEnv typing lifetime term ty resultEnv.toEnv ∧
      WellFormedEnv resultEnv.toEnv lifetime ∧
        WellFormedTy resultEnv.toEnv ty lifetime := by
  exact ⟨htyping,
    termTyping_preserves_wellFormed_for_checker hrefs hwell htyping⟩

mutual
  private theorem mutableLVal_sound :
      ∀ {fuel : Nat} {env : FiniteEnv} {lv : LVal},
        mutableLVal fuel env lv = true →
          Mutable env.toEnv lv := by
    intro fuel env lv
    cases lv with
    | var name =>
        intro h
        simp [mutableLVal] at h
        cases hlookup : env.lookup name with
        | none =>
            simp [hlookup] at h
        | some slot =>
            exact Mutable.var
              (show env.toEnv.slotAt name = some slot from hlookup)
    | deref inner =>
        intro h
        cases fuel with
        | zero =>
            simp [mutableLVal] at h
        | succ fuel =>
            cases htype : lvalType? fuel env inner with
            | none =>
                simp [mutableLVal, htype] at h
            | some result =>
                rcases result with ⟨partialTy, lifetime⟩
                cases partialTy with
                | box innerTy =>
                    simp [mutableLVal, htype] at h
                    exact Mutable.box
                      (lvalType?_sound htype)
                      (mutableLVal_sound h)
                | ty ty =>
                    cases ty with
                    | borrow mutable targets =>
                        cases mutable <;> simp [mutableLVal, htype] at h
                        exact Mutable.borrow
                          (lvalType?_sound htype)
                          (by
                            intro target htarget
                            exact mutableLVal_sound
                              (h target htarget))
                    | unit =>
                        simp [mutableLVal, htype] at h
                    | int =>
                        simp [mutableLVal, htype] at h
                    | bool =>
                        simp [mutableLVal, htype] at h
                    | box _ =>
                        simp [mutableLVal, htype] at h
                | undef _ =>
                    simp [mutableLVal, htype] at h
end

private theorem checkStrictWhile?_sound_of_termSound {fuel : Nat}
    (termSound : CheckTermSoundAt fuel) :
    ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime bodyLifetime : Lifetime}
      {condition body : Term} {result : CheckResult},
      (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
      checkStrictWhile? fuel env typing lifetime bodyLifetime condition body =
        .ok result →
        TermTyping env.toEnv typing lifetime
          (.whileLoop bodyLifetime condition body) result.ty result.env.toEnv ∧
          WellFormedEnv result.env.toEnv lifetime ∧
            WellFormedTy result.env.toEnv result.ty lifetime := by
  intro env typing lifetime bodyLifetime condition body result hrefs hwell hcheck
  unfold checkStrictWhile? at hcheck
  cases hchildCheck : isLifetimeChild lifetime bodyLifetime
  · simp [ensure, hchildCheck, Bind.bind, Except.bind] at hcheck
  · simp [ensure, hchildCheck, Bind.bind, Except.bind] at hcheck
    have hchild := isLifetimeChild_sound hchildCheck
    cases hcondition :
        checkTerm? fuel env typing lifetime condition with
    | error message =>
        simp [hcondition, Bind.bind, Except.bind] at hcheck
    | ok conditionResult =>
        simp [hcondition, Bind.bind, Except.bind] at hcheck
        by_cases hconditionTy : conditionResult.ty = .bool
        · simp [ensure, hconditionTy, Bind.bind, Except.bind] at hcheck
          have hconditionSound := termSound hrefs hwell hcondition
          have hbodyWell : WellFormedEnv conditionResult.env.toEnv bodyLifetime :=
            WellFormedEnv.of_outlives hconditionSound.2.1
              (LifetimeChild.outlives hchild)
          cases hbody :
              checkTerm? fuel conditionResult.env typing bodyLifetime body with
          | error message =>
              simp [hbody, Bind.bind, Except.bind] at hcheck
          | ok bodyResult =>
              simp [hbody, Bind.bind, Except.bind] at hcheck
              cases hbodyTyCheck :
                  wellFormedTy fuel bodyResult.env bodyResult.ty lifetime
              · simp [ensure, hbodyTyCheck, Bind.bind, Except.bind] at hcheck
              · simp [ensure, hbodyTyCheck, Bind.bind, Except.bind] at hcheck
                cases hrestore :
                    envEqOnSupport
                      (bodyResult.env.dropLifetime bodyLifetime) env
                · simp [ensure, hrestore, Bind.bind, Except.bind] at hcheck
                · simp [ensure, hrestore, Bind.bind, Except.bind] at hcheck
                  have hbodySound := termSound hrefs hbodyWell hbody
                  have hdrop :
                      bodyResult.env.toEnv.dropLifetime bodyLifetime = env.toEnv := by
                    have hsame :
                        (bodyResult.env.dropLifetime bodyLifetime).toEnv =
                          env.toEnv := by
                      exact sameBindings_toEnv_eq hrestore
                    simpa [FiniteEnv.toEnv_dropLifetime] using hsame
                  cases hcheck
                  have htyping :
                      TermTyping env.toEnv typing lifetime
                        (.whileLoop bodyLifetime condition body) .unit
                        conditionResult.env.toEnv :=
                    TermTyping.whileLoop hchild
                      (by simpa [hconditionTy] using hconditionSound.1)
                      hbodySound.1
                      (wellFormedTy_sound hbodyTyCheck)
                      hdrop
                  exact checkTermSound_of_typing hrefs hwell htyping
        · simp [ensure, hconditionTy, Bind.bind, Except.bind] at hcheck

private theorem checkWhileJoinLoop?_sound_of_termSound {fuel : Nat}
    (termSound : CheckTermSoundAt fuel) :
    ∀ {iterations : Nat} {entry inv : FiniteEnv} {typing : StoreTyping}
      {lifetime bodyLifetime : Lifetime} {condition body : Term}
      {result : CheckResult},
      (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
      LifetimeChild lifetime bodyLifetime →
      WellFormedEnv entry.toEnv lifetime →
      WellFormedEnv inv.toEnv lifetime →
      checkWhileJoinLoop? iterations fuel entry inv typing lifetime
        bodyLifetime condition body = .ok result →
        TermTyping entry.toEnv typing lifetime
          (.whileLoop bodyLifetime condition body) result.ty result.env.toEnv ∧
          WellFormedEnv result.env.toEnv lifetime ∧
            WellFormedTy result.env.toEnv result.ty lifetime := by
  intro iterations
  induction iterations with
  | zero =>
      intro entry inv typing lifetime bodyLifetime condition body result
        hrefs hchild hentryWell hinvWell hcheck
      simp [checkWhileJoinLoop?] at hcheck
  | succ iterations ih =>
      intro entry inv typing lifetime bodyLifetime condition body result
        hrefs hchild hentryWell hinvWell hcheck
      simp [checkWhileJoinLoop?] at hcheck
      cases hcondition :
          checkTerm? fuel inv typing lifetime condition with
      | error message =>
          simp [hcondition, Bind.bind, Except.bind] at hcheck
      | ok conditionResult =>
        simp [hcondition, Bind.bind, Except.bind] at hcheck
        by_cases hconditionTy : conditionResult.ty = .bool
        · simp [ensure, hconditionTy, Bind.bind, Except.bind] at hcheck
          have hconditionSound := termSound hrefs hinvWell hcondition
          have hbodyWell :
              WellFormedEnv conditionResult.env.toEnv bodyLifetime :=
            WellFormedEnv.of_outlives hconditionSound.2.1
              (LifetimeChild.outlives hchild)
          cases hbody :
              checkTerm? fuel conditionResult.env typing bodyLifetime body with
            | error message =>
                simp [hbody, Bind.bind, Except.bind] at hcheck
            | ok bodyResult =>
                simp [hbody, Bind.bind, Except.bind] at hcheck
                cases hbodyTyCheck :
                    wellFormedTy fuel bodyResult.env bodyResult.ty lifetime
                · simp [ensure, hbodyTyCheck, Bind.bind, Except.bind] at hcheck
                · simp [ensure, hbodyTyCheck, Bind.bind, Except.bind] at hcheck
                  let back := bodyResult.env.dropLifetime bodyLifetime
                  cases hjoin : envJoin? entry back with
                  | none =>
                      simp [back, fromOption, hjoin, Bind.bind, Except.bind] at hcheck
                  | some nextInv =>
                      simp [back, fromOption, hjoin, Bind.bind, Except.bind] at hcheck
                      cases hentryShape : envJoinSameShape entry nextInv
                      · simp [ensure, hentryShape, Bind.bind, Except.bind] at hcheck
                      · simp [ensure, hentryShape, Bind.bind, Except.bind] at hcheck
                        cases hbackShape : envJoinSameShape back nextInv
                        · simp [back, ensure, hbackShape, Bind.bind, Except.bind] at hcheck
                        · simp [back, ensure, hbackShape, Bind.bind, Except.bind] at hcheck
                          cases hkit : wellFormedKit fuel nextInv
                          · simp [ensure, hkit, Bind.bind, Except.bind] at hcheck
                          · simp [ensure, hkit, Bind.bind, Except.bind] at hcheck
                            have hbodySound := termSound hrefs hbodyWell hbody
                            have hjoinSound : EnvJoin entry.toEnv back.toEnv nextInv.toEnv :=
                              envJoin?_sound hjoin
                            have hkitSound := wellFormedKit_sound hkit
                            have hnextWell : WellFormedEnv nextInv.toEnv lifetime :=
                              ⟨hkitSound.1,
                                EnvSlotsOutlive.of_lifetimesPreserved
                                  hentryWell.2.1
                                  (EnvJoin.lifetimesPreserved_left hjoinSound),
                                wellFormedKit_coherent_sound hkit,
                                hkitSound.2.2⟩
                            cases hfixed : envEqOnSupport nextInv inv
                            · simp [hfixed, Bind.bind, Except.bind] at hcheck
                              exact ih hrefs hchild hentryWell hnextWell hcheck
                            · simp [hfixed, Bind.bind, Except.bind] at hcheck
                              cases hentryCondition :
                                  checkTerm? fuel entry typing lifetime condition with
                              | error message =>
                                  simp [hentryCondition, Bind.bind, Except.bind] at hcheck
                              | ok entryCondition =>
                                  simp [hentryCondition, Bind.bind, Except.bind] at hcheck
                                  by_cases hentryConditionTy :
                                      entryCondition.ty = .bool
                                  · simp [ensure, hentryConditionTy,
                                      Bind.bind, Except.bind] at hcheck
                                    have hentryConditionSound :=
                                      termSound hrefs hentryWell hentryCondition
                                    have hentryBodyWell :
                                        WellFormedEnv entryCondition.env.toEnv
                                          bodyLifetime :=
                                      WellFormedEnv.of_outlives
                                        hentryConditionSound.2.1
                                        (LifetimeChild.outlives hchild)
                                    cases hentryBody :
                                        checkTerm? fuel entryCondition.env typing
                                          bodyLifetime body with
                                    | error message =>
                                        simp [hentryBody, Bind.bind, Except.bind,
                                          discard, Functor.mapConst, Except.map]
                                          at hcheck
                                    | ok entryBody =>
                                        simp [hentryBody, Bind.bind, Except.bind]
                                          at hcheck
                                        cases hcheck
                                        have hsame :
                                            nextInv.toEnv = inv.toEnv :=
                                          sameBindings_toEnv_eq hfixed
                                        have hjoinInv :
                                            EnvJoin entry.toEnv back.toEnv inv.toEnv := by
                                          simpa [hsame] using hjoinSound
                                        have hentryShapeInv :
                                            EnvJoinSameShape entry.toEnv inv.toEnv := by
                                          simpa [hsame] using
                                            envJoinSameShape_sound hentryShape
                                        have hbackShapeInv :
                                            EnvJoinSameShape back.toEnv inv.toEnv := by
                                          simpa [hsame] using
                                            envJoinSameShape_sound hbackShape
                                        have hcontainedInv :
                                            ContainedBorrowsWellFormed inv.toEnv := by
                                          simpa [hsame] using hkitSound.1
                                        have hcoherentInv : Coherent inv.toEnv := by
                                          simpa [hsame] using
                                            wellFormedKit_coherent_sound hkit
                                        have hlinearInv : Linearizable inv.toEnv := by
                                          simpa [hsame] using hkitSound.2.2
                                        have hdrop :
                                            bodyResult.env.toEnv.dropLifetime
                                              bodyLifetime = back.toEnv := by
                                          simp [back, FiniteEnv.toEnv_dropLifetime]
                                        have hentryBodySound :=
                                          termSound hrefs hentryBodyWell hentryBody
                                        have htyping :
                                            TermTyping entry.toEnv typing lifetime
                                              (.whileLoop bodyLifetime condition body)
                                              .unit conditionResult.env.toEnv :=
                                          TermTyping.whileLoopJoin hchild
                                            hjoinInv hentryShapeInv hbackShapeInv
                                            hcontainedInv hcoherentInv hlinearInv
                                            (by simpa [hconditionTy] using
                                              hconditionSound.1)
                                            hbodySound.1
                                            (wellFormedTy_sound hbodyTyCheck)
                                            hdrop
                                            (by simpa [hentryConditionTy] using
                                              hentryConditionSound.1)
                                            hentryBodySound.1
                                        exact checkTermSound_of_typing hrefs
                                          hentryWell htyping
                                  · simp [ensure, hentryConditionTy,
                                      Bind.bind, Except.bind] at hcheck
        · simp [ensure, hconditionTy, Bind.bind, Except.bind] at hcheck

private theorem checkWhileJoin?_sound_of_termSound {fuel : Nat}
    (termSound : CheckTermSoundAt fuel) :
    ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime bodyLifetime : Lifetime}
      {condition body : Term} {result : CheckResult},
      (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
      checkWhileJoin? fuel env typing lifetime bodyLifetime condition body =
        .ok result →
        TermTyping env.toEnv typing lifetime
          (.whileLoop bodyLifetime condition body) result.ty result.env.toEnv ∧
          WellFormedEnv result.env.toEnv lifetime ∧
            WellFormedTy result.env.toEnv result.ty lifetime := by
  intro env typing lifetime bodyLifetime condition body result hrefs hwell hcheck
  unfold checkWhileJoin? at hcheck
  cases hchildCheck : isLifetimeChild lifetime bodyLifetime
  · simp [ensure, hchildCheck, Bind.bind, Except.bind] at hcheck
  · simp [ensure, hchildCheck, Bind.bind, Except.bind] at hcheck
    exact checkWhileJoinLoop?_sound_of_termSound termSound
      hrefs (isLifetimeChild_sound hchildCheck) hwell hwell hcheck

private theorem checkWhile?_sound_of_termSound {fuel : Nat}
    (termSound : CheckTermSoundAt fuel) :
    ∀ {env : FiniteEnv} {typing : StoreTyping} {lifetime bodyLifetime : Lifetime}
      {condition body : Term} {result : CheckResult},
      (∀ env lifetime, CheckerStoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
      checkWhile? fuel env typing lifetime bodyLifetime condition body =
        .ok result →
        TermTyping env.toEnv typing lifetime
          (.whileLoop bodyLifetime condition body) result.ty result.env.toEnv ∧
          WellFormedEnv result.env.toEnv lifetime ∧
            WellFormedTy result.env.toEnv result.ty lifetime := by
  intro env typing lifetime bodyLifetime condition body result hrefs hwell hcheck
  unfold checkWhile? at hcheck
  cases hstrict :
      checkStrictWhile? fuel env typing lifetime bodyLifetime condition body with
  | ok strictResult =>
      simp [hstrict] at hcheck
      cases hcheck
      exact checkStrictWhile?_sound_of_termSound termSound hrefs hwell hstrict
  | error message =>
      simp [hstrict] at hcheck
      cases hdiv : termDiverges body
      · simp [hdiv] at hcheck
        exact checkWhileJoin?_sound_of_termSound termSound hrefs hwell hcheck
      · simp [hdiv] at hcheck

private theorem checkTerm?_sound_at : ∀ fuel, CheckTermSoundAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro env typing lifetime term result _hrefs _hwell hcheck
      cases term <;> simp [checkTerm?] at hcheck
  | succ fuel ih =>
      intro env typing lifetime term result hrefs hwell hcheck
      cases term with
      | val value =>
          simp [checkTerm?] at hcheck
          cases hty : valueTy? typing value with
          | none =>
              simp [hty, fromOption, Bind.bind, Except.bind] at hcheck
          | some ty =>
              simp [hty, fromOption, Bind.bind, Except.bind] at hcheck
              cases hcheck
              exact checkTermSound_of_typing hrefs hwell
                (TermTyping.const (valueTy?_sound hty))
      | missing =>
          simp [checkTerm?] at hcheck
      | copy lv =>
          simp [checkTerm?] at hcheck
          cases hlv : lvalType? fuel env lv with
          | none =>
              by_cases hfits : lvalFitsFuel fuel lv <;>
                simp [lvalTypeOrError?, hlv, hfits, fromOption, Bind.bind,
                  Except.bind] at hcheck
          | some typed =>
              rcases typed with ⟨partialTy, valueLifetime⟩
              cases partialTy with
              | ty ty =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
                  cases hcopy : copyTy ty
                  · simp [ensure, hcopy, Bind.bind, Except.bind] at hcheck
                  · simp [ensure, hcopy, Bind.bind, Except.bind] at hcheck
                    cases hread : readProhibited env lv
                    · simp [ensure, hread, Bind.bind, Except.bind] at hcheck
                      cases hcheck
                      exact checkTermSound_of_typing hrefs hwell
                        (TermTyping.copy (lvalType?_sound hlv)
                          (copyTy_sound hcopy)
                          (readProhibited_false_sound hread))
                    · simp [ensure, hread, Bind.bind, Except.bind] at hcheck
              | box _ =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
              | undef _ =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
      | move lv =>
          simp [checkTerm?] at hcheck
          cases hlv : lvalType? fuel env lv with
          | none =>
              by_cases hfits : lvalFitsFuel fuel lv <;>
                simp [lvalTypeOrError?, hlv, hfits, fromOption, Bind.bind,
                  Except.bind] at hcheck
          | some typed =>
              rcases typed with ⟨partialTy, valueLifetime⟩
              cases partialTy with
              | ty ty =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
                  cases hwriteProhibited : writeProhibited env lv
                  · simp [ensure, hwriteProhibited, Bind.bind, Except.bind]
                      at hcheck
                    cases hmoved : envMove? env lv with
                    | none =>
                        simp [hmoved, fromOption, Bind.bind, Except.bind]
                          at hcheck
                    | some moved =>
                        simp [hmoved, fromOption, Bind.bind, Except.bind]
                          at hcheck
                        cases hcheck
                        exact checkTermSound_of_typing hrefs hwell
                          (TermTyping.move (lvalType?_sound hlv)
                            (writeProhibited_false_sound hwriteProhibited)
                            (envMove?_sound hmoved))
                  · simp [ensure, hwriteProhibited, Bind.bind, Except.bind]
                      at hcheck
              | box _ =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
              | undef _ =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
      | borrow mutable lv =>
          simp [checkTerm?] at hcheck
          cases hlv : lvalType? fuel env lv with
          | none =>
              by_cases hfits : lvalFitsFuel fuel lv <;>
                simp [lvalTypeOrError?, hlv, hfits, fromOption, Bind.bind,
                  Except.bind] at hcheck
          | some typed =>
              rcases typed with ⟨partialTy, valueLifetime⟩
              cases partialTy with
              | ty ty =>
                  cases mutable with
                  | false =>
                      simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
                      cases hread : readProhibited env lv
                      · simp [ensure, hread, Bind.bind, Except.bind] at hcheck
                        cases hcheck
                        exact checkTermSound_of_typing hrefs hwell
                          (TermTyping.immBorrow (lvalType?_sound hlv)
                            (readProhibited_false_sound hread))
                      · simp [ensure, hread, Bind.bind, Except.bind] at hcheck
                  | true =>
                      simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
                      cases hmutable : mutableLVal fuel env lv
                      · simp [ensure, hmutable, Bind.bind, Except.bind]
                          at hcheck
                      · simp [ensure, hmutable, Bind.bind, Except.bind]
                          at hcheck
                        cases hwrite : writeProhibited env lv
                        · simp [ensure, hwrite, Bind.bind, Except.bind]
                            at hcheck
                          cases hcheck
                          exact checkTermSound_of_typing hrefs hwell
                            (TermTyping.mutBorrow (lvalType?_sound hlv)
                              (mutableLVal_sound hmutable)
                              (writeProhibited_false_sound hwrite))
                        · simp [ensure, hwrite, Bind.bind, Except.bind]
                            at hcheck
              | box _ =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
              | undef _ =>
                  simp [hlv, fromOption, Bind.bind, Except.bind] at hcheck
      | box operand =>
          simp [checkTerm?] at hcheck
          cases hoperand : checkTerm? fuel env typing lifetime operand with
          | error message =>
              simp [hoperand, Bind.bind, Except.bind] at hcheck
          | ok operandResult =>
              simp [hoperand, Bind.bind, Except.bind] at hcheck
              cases hcheck
              have hoperandSound := ih hrefs hwell hoperand
              exact checkTermSound_of_typing hrefs hwell
                (TermTyping.box hoperandSound.1)
      | block blockLifetime terms =>
          simp [checkTerm?] at hcheck
          cases hchildCheck : isLifetimeChild lifetime blockLifetime
          · simp [ensure, hchildCheck, Bind.bind, Except.bind] at hcheck
          · simp [ensure, hchildCheck, Bind.bind, Except.bind] at hcheck
            have hchild := isLifetimeChild_sound hchildCheck
            have hbodyWell : WellFormedEnv env.toEnv blockLifetime :=
              WellFormedEnv.weaken hwell (LifetimeChild.outlives hchild)
            cases hbody :
                checkTermList? fuel env typing blockLifetime terms with
            | error message =>
                simp [hbody, Bind.bind, Except.bind] at hcheck
            | ok bodyResult =>
                simp [hbody, Bind.bind, Except.bind] at hcheck
                cases hbodyTyCheck :
                    wellFormedTy fuel bodyResult.env bodyResult.ty lifetime
                · simp [ensure, hbodyTyCheck, Bind.bind, Except.bind] at hcheck
                · simp [ensure, hbodyTyCheck, Bind.bind, Except.bind] at hcheck
                  cases hcheck
                  have hbodySound :=
                    checkTermList?_sound_of_termSound ih hrefs hbodyWell hbody
                  have htyping :
                      TermTyping env.toEnv typing lifetime
                        (.block blockLifetime terms) bodyResult.ty
                        (bodyResult.env.dropLifetime blockLifetime).toEnv :=
                    TermTyping.block hchild hbodySound.1
                      (wellFormedTy_sound hbodyTyCheck)
                      (by simp [FiniteEnv.toEnv_dropLifetime])
                  exact checkTermSound_of_typing hrefs hwell htyping
      | letMut name initialiser =>
          simp [checkTerm?] at hcheck
          cases hfreshIn : env.fresh name
          · simp [ensure, hfreshIn, Bind.bind, Except.bind] at hcheck
          · simp [ensure, hfreshIn, Bind.bind, Except.bind] at hcheck
            cases hinitialiser :
                checkTerm? fuel env typing lifetime initialiser with
            | error message =>
                simp [hinitialiser, Bind.bind, Except.bind] at hcheck
            | ok initResult =>
                simp [hinitialiser, Bind.bind, Except.bind] at hcheck
                have hinitSound := ih hrefs hwell hinitialiser
                cases hfreshOut : initResult.env.fresh name
                · simp [ensure, hfreshOut, Bind.bind, Except.bind] at hcheck
                · simp [ensure, hfreshOut, Bind.bind, Except.bind] at hcheck
                  let updated :=
                    initResult.env.update name
                      { ty := .ty initResult.ty, lifetime := lifetime }
                  cases hkit : wellFormedKit fuel updated
                  · simp [updated, ensure, hkit, Bind.bind, Except.bind]
                      at hcheck
                  · simp [updated, ensure, hkit, Bind.bind, Except.bind]
                      at hcheck
                    cases hcheck
                    have hcoherence :
                        FreshUpdateCoherenceObligations initResult.env.toEnv
                          name initResult.ty lifetime :=
                      freshUpdateCoherenceObligations_of_checker
                        (env := initResult.env) (updated := updated)
                        (name := name) (ty := initResult.ty)
                        (lifetime := lifetime) rfl
                        hinitSound.2.1.1 hinitSound.2.2
                        (FiniteEnv.fresh_sound hfreshOut) hkit
                    have htyping :
                        TermTyping env.toEnv typing lifetime
                          (.letMut name initialiser) .unit updated.toEnv :=
                      TermTyping.declare (FiniteEnv.fresh_sound hfreshIn)
                        hinitSound.1 (FiniteEnv.fresh_sound hfreshOut) hcoherence
                        (by simp [updated, FiniteEnv.toEnv_update])
                    exact checkTermSound_of_typing hrefs hwell htyping
      | assign lhs rhs =>
          simp [checkTerm?] at hcheck
          cases hlhsBefore : lvalType? fuel env lhs with
          | none =>
              by_cases hfits : lvalFitsFuel fuel lhs <;>
                simp [lvalTypeOrError?, hlhsBefore, hfits, fromOption,
                  Bind.bind, Except.bind] at hcheck
          | some lhsBefore =>
              rcases lhsBefore with ⟨oldTy, targetLifetime⟩
              simp [hlhsBefore, fromOption, Bind.bind, Except.bind] at hcheck
              cases hrhs : checkTerm? fuel env typing lifetime rhs with
              | error message =>
                  simp [hrhs, Bind.bind, Except.bind] at hcheck
              | ok rhsResult =>
                  simp [hrhs, Bind.bind, Except.bind] at hcheck
                  have hrhsSound := ih hrefs hwell hrhs
                  cases hlhsAfter :
                      lvalType? fuel rhsResult.env lhs with
                  | none =>
                      by_cases hfits : lvalFitsFuel fuel lhs <;>
                        simp [lvalTypeOrError?, hlhsAfter, hfits,
                          fromOption, Bind.bind, Except.bind] at hcheck
                  | some lhsAfter =>
                      rcases lhsAfter with ⟨oldTyAfter, targetLifetimeAfter⟩
                      simp [hlhsAfter, fromOption, Bind.bind, Except.bind]
                        at hcheck
                      by_cases hOldEq : (oldTyAfter = oldTy)
                      ·
                        by_cases hLifetimeEq :
                            (targetLifetimeAfter = targetLifetime)
                        ·
                          simp [ensure, hOldEq, hLifetimeEq, Bind.bind,
                            Except.bind] at hcheck
                          subst oldTyAfter
                          subst targetLifetimeAfter
                          cases hshape :
                              shapeCompatiblePartialTy fuel rhsResult.env
                                oldTy (.ty rhsResult.ty)
                          · simp [ensure, hshape, Bind.bind, Except.bind]
                              at hcheck
                          · simp [ensure, hshape, Bind.bind, Except.bind]
                              at hcheck
                            cases hwellRhs :
                                wellFormedTy fuel rhsResult.env
                                  rhsResult.ty targetLifetime
                            · simp [ensure, hwellRhs, Bind.bind,
                                Except.bind] at hcheck
                            · simp [ensure, hwellRhs, Bind.bind,
                                Except.bind] at hcheck
                              cases hwrite :
                                  envWrite? fuel 0 rhsResult.env lhs
                                    rhsResult.ty with
                              | none =>
                                  simp [hwrite, fromOption, Bind.bind,
                                    Except.bind] at hcheck
                              | some written =>
                                  simp [hwrite, fromOption, Bind.bind,
                                    Except.bind] at hcheck
                                  cases houtside :
                                      envEqOutside rhsResult.env written
                                        (LVal.base lhs)
                                  · simp [ensure, houtside, Bind.bind,
                                      Except.bind] at hcheck
                                  · simp [ensure, houtside, Bind.bind,
                                      Except.bind] at hcheck
                                    cases hbelow :
                                        rhsBorrowTargetsBelow rhsResult.env
                                          written rhsResult.ty
                                    · simp [ensure, hbelow, Bind.bind,
                                        Except.bind] at hcheck
                                    · simp [ensure, hbelow, Bind.bind,
                                        Except.bind] at hcheck
                                      by_cases hcontained :
                                          containedBorrowsWellFormed fuel
                                            written = true
                                      · by_cases hlinear :
                                            linearizable written = true
                                        · have hinvariants :
                                            (containedBorrowsWellFormed fuel
                                                written &&
                                              linearizable written) = true := by
                                            simp [hcontained, hlinear]
                                          simp [ensure, hcontained, hlinear,
                                            Bind.bind, Except.bind] at hcheck
                                          cases hcoherentNonempty :
                                              coherentNonempty fuel written
                                          · simp [ensure, hcoherentNonempty,
                                              Bind.bind, Except.bind] at hcheck
                                          · simp [ensure, hcoherentNonempty,
                                              Bind.bind, Except.bind] at hcheck
                                            cases hrootCoherent :
                                                rootCoherent fuel written
                                                  (LVal.base lhs)
                                            · simp [ensure, hrootCoherent,
                                                Bind.bind, Except.bind]
                                                at hcheck
                                            · simp [ensure, hrootCoherent,
                                                Bind.bind, Except.bind]
                                                at hcheck
                                              cases hnotWrite :
                                                  writeProhibited written lhs
                                              · simp [ensure, hnotWrite,
                                                  Bind.bind, Except.bind]
                                                  at hcheck
                                                cases hcheck
                                                have hinv :=
                                                  assignmentResultInvariants_sound
                                                    hinvariants
                                                have hnotWriteProp :=
                                                  writeProhibited_false_sound
                                                    hnotWrite
                                                have htyping :
                                                    TermTyping env.toEnv typing
                                                      lifetime (.assign lhs rhs)
                                                      .unit written.toEnv :=
                                                  TermTyping.assign
                                                    (lvalType?_sound
                                                      hlhsBefore)
                                                    hrhsSound.1
                                                    (lvalType?_sound hlhsAfter)
                                                    (shapeCompatiblePartialTy_sound
                                                      hshape)
                                                    (wellFormedTy_sound
                                                      hwellRhs)
                                                    (envWrite?_sound hwrite)
                                                    (rhsBorrowTargetsBelow_sound
                                                      hbelow)
                                                    (envWriteCoherenceObligations_of_checker
                                                      houtside
                                                      hcoherentNonempty
                                                      hrootCoherent hinv.2
                                                      hnotWriteProp)
                                                    hinv.1 hnotWriteProp
                                                exact checkTermSound_of_typing
                                                  hrefs hwell htyping
                                              · simp [ensure, hnotWrite,
                                                  Bind.bind, Except.bind]
                                                  at hcheck
                                        · simp [ensure, hcontained, hlinear,
                                            Bind.bind, Except.bind] at hcheck
                                      · simp [ensure, hcontained, Bind.bind,
                                          Except.bind] at hcheck
                        ·
                          simp [ensure, hOldEq, hLifetimeEq, Bind.bind,
                            Except.bind] at hcheck
                      · simp [ensure, hOldEq, Bind.bind, Except.bind] at hcheck
      | eq lhs rhs =>
          simp [checkTerm?] at hcheck
          cases hlhs : checkTerm? fuel env typing lifetime lhs with
          | error message =>
              simp [hlhs, Bind.bind, Except.bind] at hcheck
          | ok lhsResult =>
              simp [hlhs, Bind.bind, Except.bind] at hcheck
              have hlhsSound := ih hrefs hwell hlhs
              cases hlhsCopy : copyTy lhsResult.ty
              · simp [ensure, hlhsCopy, Bind.bind, Except.bind] at hcheck
              · simp [ensure, hlhsCopy, Bind.bind, Except.bind] at hcheck
                let ghost := freshGhostName lhsResult.env rhs
                cases hghostFresh : lhsResult.env.fresh ghost
                · simp [ghost, ensure, hghostFresh, Bind.bind, Except.bind]
                    at hcheck
                · simp [ghost, ensure, hghostFresh, Bind.bind, Except.bind]
                    at hcheck
                  let ghostEnv :=
                    lhsResult.env.update ghost
                      { ty := .ty lhsResult.ty, lifetime := lifetime }
                  cases hghostKit : wellFormedKit fuel ghostEnv
                  · simp [ghost, ghostEnv, ensure, hghostKit, Bind.bind,
                      Except.bind] at hcheck
                  · simp [ghost, ghostEnv, ensure, hghostKit, Bind.bind,
                      Except.bind] at hcheck
                    have hghostKitSound := wellFormedKit_sound hghostKit
                    have hghostWell : WellFormedEnv ghostEnv.toEnv lifetime :=
                      ⟨hghostKitSound.1,
                        by
                          simpa [ghostEnv, FiniteEnv.toEnv_update] using
                            envSlotsOutlive_update_fresh_current
                              hlhsSound.2.1.2.1
                              (FiniteEnv.fresh_sound hghostFresh),
                        wellFormedKit_coherent_sound hghostKit,
                        hghostKitSound.2.2⟩
                    cases hghost :
                        checkTerm? fuel ghostEnv typing lifetime rhs with
                    | error message =>
                        have hfalse : False := by
                          simpa [ghost, ghostEnv, hghost, Bind.bind,
                            Except.bind, discard, Functor.mapConst,
                            Except.map] using hcheck
                        exact False.elim hfalse
                    | ok ghostResult =>
                        simp [hghost, Bind.bind, Except.bind, discard,
                          Functor.mapConst, Except.map] at hcheck
                        have hghostSound := ih hrefs hghostWell hghost
                        cases hrhs :
                            checkTerm? fuel lhsResult.env typing lifetime rhs with
                        | error message =>
                            have hfalse : False := by
                              simpa [ghost, ghostEnv, hghost, hrhs,
                                Bind.bind, Except.bind, discard,
                                Functor.mapConst, Except.map] using hcheck
                            exact False.elim hfalse
                        | ok rhsResult =>
                            simp [hrhs, Bind.bind, Except.bind] at hcheck
                            have hrhsSound := ih hrefs hlhsSound.2.1 hrhs
                            cases hrhsCopy : copyTy rhsResult.ty
                            · have hfalse : False := by
                                simpa [ghost, ghostEnv, hghost, hrhs,
                                  hrhsCopy, ensure, Bind.bind, Except.bind,
                                  discard, Functor.mapConst, Except.map]
                                  using hcheck
                              exact False.elim hfalse
                            · simp [ensure, hrhsCopy, Bind.bind, Except.bind]
                                at hcheck
                              cases hshape :
                                    shapeCompatiblePartialTy fuel rhsResult.env
                                    (.ty lhsResult.ty) (.ty rhsResult.ty)
                              · have hfalse : False := by
                                  simpa [ghost, ghostEnv, hghost, hrhs,
                                    hrhsCopy, hshape, ensure, Bind.bind,
                                    Except.bind, discard, Functor.mapConst,
                                    Except.map] using hcheck
                                exact False.elim hfalse
                              · simp [ensure, hshape, Bind.bind, Except.bind]
                                  at hcheck
                                have hresultOk :
                                    (Except.ok
                                        { ty := Ty.bool, env := rhsResult.env } :
                                      Except String CheckResult) =
                                      Except.ok result := by
                                  simpa [ghost, ghostEnv, hghost, hrhs,
                                    hrhsCopy, hshape, ensure, Bind.bind,
                                    Except.bind, discard, Functor.mapConst,
                                    Except.map] using hcheck
                                have hresult :
                                    result =
                                      { ty := Ty.bool, env := rhsResult.env } :=
                                  (Except.ok.inj hresultOk).symm
                                cases hresult
                                have htyping :
                                    TermTyping env.toEnv typing lifetime
                                      (.eq lhs rhs) .bool rhsResult.env.toEnv :=
                                  TermTyping.eq (ghost := ghost) hlhsSound.1
                                    (FiniteEnv.fresh_sound hghostFresh)
                                    (by
                                      simpa [ghostEnv, FiniteEnv.toEnv_update]
                                        using hghostSound.1)
                                    hrhsSound.1 (copyTy_sound hlhsCopy)
                                    (copyTy_sound hrhsCopy)
                                    (shapeCompatiblePartialTy_sound hshape)
                                exact checkTermSound_of_typing hrefs hwell
                                  htyping
      | ite condition trueBranch falseBranch =>
          simp [checkTerm?] at hcheck
          cases hcondition :
              checkTerm? fuel env typing lifetime condition with
          | error message =>
              simp [hcondition, Bind.bind, Except.bind] at hcheck
          | ok conditionResult =>
              simp [hcondition, Bind.bind, Except.bind] at hcheck
              have hconditionSound := ih hrefs hwell hcondition
              by_cases hconditionTy : conditionResult.ty = .bool
              · simp [ensure, hconditionTy, Bind.bind, Except.bind] at hcheck
                cases htrue :
                    checkTerm? fuel conditionResult.env typing lifetime
                      trueBranch with
                | error message =>
                    simp [htrue, Bind.bind, Except.bind] at hcheck
                | ok thenResult =>
                    simp [htrue, Bind.bind, Except.bind] at hcheck
                    have hthenSound := ih hrefs hconditionSound.2.1 htrue
                    cases hfalse :
                        checkTerm? fuel conditionResult.env typing lifetime
                          falseBranch with
                    | error message =>
                        simp [hfalse, Bind.bind, Except.bind] at hcheck
                    | ok falseResult =>
                        simp [hfalse, Bind.bind, Except.bind] at hcheck
                        have hfalseSound := ih hrefs hconditionSound.2.1 hfalse
                        cases hjoinTy :
                            partialTyJoin? (.ty (CheckResult.ty thenResult))
                              (.ty falseResult.ty) with
                        | none =>
                            simp [hjoinTy] at hcheck
                            cases hdiv : termDiverges falseBranch
                            · simp [hdiv] at hcheck
                            · simp [hdiv] at hcheck
                              have htyping :
                                  TermTyping env.toEnv typing lifetime
                                    (.ite condition trueBranch falseBranch)
                                    (CheckResult.ty thenResult)
                                    (CheckResult.env thenResult).toEnv :=
                                TermTyping.iteDiverging
                                  (by simpa [hconditionTy] using
                                    hconditionSound.1)
                                  hthenSound.1 hfalseSound.1
                                  (termDiverges_sound hdiv)
                              cases hcheck
                              exact checkTermSound_of_typing hrefs hwell
                                htyping
                        | some joinPartial =>
                            cases joinPartial with
                            | ty joinTy =>
                                cases hjoinEnv :
                                    envJoin? (CheckResult.env thenResult)
                                      falseResult.env with
                                | none =>
                                    simp [hjoinTy, hjoinEnv] at hcheck
                                    cases hdiv : termDiverges falseBranch
                                    · simp [hdiv] at hcheck
                                    · simp [hdiv] at hcheck
                                      have htyping :
                                          TermTyping env.toEnv typing lifetime
                                            (.ite condition trueBranch
                                              falseBranch)
                                            (CheckResult.ty thenResult)
                                            (CheckResult.env thenResult).toEnv :=
                                        TermTyping.iteDiverging
                                          (by simpa [hconditionTy] using
                                            hconditionSound.1)
                                          hthenSound.1 hfalseSound.1
                                          (termDiverges_sound hdiv)
                                      cases hcheck
                                      exact checkTermSound_of_typing hrefs
                                        hwell htyping
                                | some joinEnv =>
                                    simp [hjoinTy, hjoinEnv] at hcheck
                                    cases hthenShape :
                                        envJoinSameShape
                                          (CheckResult.env thenResult) joinEnv
                                    · simp [ensure, hthenShape, Bind.bind,
                                        Except.bind] at hcheck
                                    · simp [ensure, hthenShape, Bind.bind,
                                        Except.bind] at hcheck
                                      cases hfalseShape :
                                          envJoinSameShape falseResult.env
                                            joinEnv
                                      · simp [ensure, hfalseShape, Bind.bind,
                                          Except.bind] at hcheck
                                      · simp [ensure, hfalseShape, Bind.bind,
                                          Except.bind] at hcheck
                                        cases hwellJoin :
                                            wellFormedTy fuel joinEnv joinTy
                                              lifetime
                                        · simp [ensure, hwellJoin, Bind.bind,
                                            Except.bind] at hcheck
                                        · simp [ensure, hwellJoin, Bind.bind,
                                            Except.bind] at hcheck
                                          cases hkit :
                                              wellFormedKit fuel joinEnv
                                          · simp [ensure, hkit, Bind.bind,
                                              Except.bind] at hcheck
                                          · simp [ensure, hkit, Bind.bind,
                                              Except.bind] at hcheck
                                            cases hcheck
                                            have hkitSound :=
                                              wellFormedKit_sound hkit
                                            have htyping :
                                                TermTyping env.toEnv typing
                                                  lifetime
                                                  (.ite condition trueBranch
                                                    falseBranch)
                                                  joinTy joinEnv.toEnv :=
                                              TermTyping.ite
                                                (by simpa [hconditionTy]
                                                  using hconditionSound.1)
                                                hthenSound.1 hfalseSound.1
                                                (partialTyJoin?_sound
                                                  hjoinTy)
                                                (envJoin?_sound hjoinEnv)
                                                (envJoinSameShape_sound
                                                  hthenShape)
                                                (envJoinSameShape_sound
                                                  hfalseShape)
                                                (wellFormedTy_sound
                                                  hwellJoin)
                                                hkitSound.1
                                                (wellFormedKit_coherent_sound
                                                  hkit)
                                                hkitSound.2.2
                                            exact checkTermSound_of_typing
                                              hrefs hwell htyping
                            | box _ =>
                                simp [hjoinTy] at hcheck
                                cases hdiv : termDiverges falseBranch
                                · simp [hdiv] at hcheck
                                · simp [hdiv] at hcheck
                                  have htyping :
                                      TermTyping env.toEnv typing lifetime
                                        (.ite condition trueBranch falseBranch)
                                        (CheckResult.ty thenResult)
                                        (CheckResult.env thenResult).toEnv :=
                                    TermTyping.iteDiverging
                                      (by simpa [hconditionTy] using
                                        hconditionSound.1)
                                      hthenSound.1 hfalseSound.1
                                      (termDiverges_sound hdiv)
                                  cases hcheck
                                  exact checkTermSound_of_typing hrefs hwell
                                    htyping
                            | undef _ =>
                                simp [hjoinTy] at hcheck
                                cases hdiv : termDiverges falseBranch
                                · simp [hdiv] at hcheck
                                · simp [hdiv] at hcheck
                                  have htyping :
                                      TermTyping env.toEnv typing lifetime
                                        (.ite condition trueBranch falseBranch)
                                        (CheckResult.ty thenResult)
                                        (CheckResult.env thenResult).toEnv :=
                                    TermTyping.iteDiverging
                                      (by simpa [hconditionTy] using
                                        hconditionSound.1)
                                      hthenSound.1 hfalseSound.1
                                      (termDiverges_sound hdiv)
                                  cases hcheck
                                  exact checkTermSound_of_typing hrefs hwell
                                    htyping
              · simp [ensure, hconditionTy] at hcheck
      | whileLoop bodyLifetime condition body =>
          have hwhile :
              checkWhile? fuel env typing lifetime bodyLifetime condition body =
                .ok result := by
            simpa [checkTerm?] using hcheck
          exact checkWhile?_sound_of_termSound ih hrefs hwell hwhile
      | whileCond bodyLifetime conditionInFlight condition body =>
          simp [checkTerm?] at hcheck
      | whileBody bodyLifetime bodyInFlight condition body =>
          simp [checkTerm?] at hcheck

theorem checkTerm?_sound {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {result : CheckResult} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
        checkTerm? fuel env typing lifetime term = .ok result →
          TermTyping env.toEnv typing lifetime term result.ty
            result.env.toEnv := by
  intro hrefs hwell hcheck
  have hrefsChecker :
      ∀ env lifetime,
        CheckerStoreTypingRefsWellFormed env typing lifetime := by
    intro env lifetime ref ty hlookup
    exact hrefs env lifetime ref ty hlookup
  exact (checkTerm?_sound_at fuel hrefsChecker hwell hcheck).1

theorem checkTermList?_sound {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {terms : List Term}
    {result : CheckResult} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
        checkTermList? fuel env typing lifetime terms = .ok result →
          TermListTyping env.toEnv typing lifetime terms result.ty
            result.env.toEnv := by
  intro hrefs hwell hcheck
  have hrefsChecker :
      ∀ env lifetime,
        CheckerStoreTypingRefsWellFormed env typing lifetime := by
    intro env lifetime ref ty hlookup
    exact hrefs env lifetime ref ty hlookup
  exact (checkTermList?_sound_of_termSound (checkTerm?_sound_at fuel)
    hrefsChecker hwell hcheck).1

theorem termTyping_of_checkTermMatches? {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {term : Term}
    {expectedTy : Ty} {expectedEnv : FiniteEnv} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
        checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv =
          true →
          TermTyping env.toEnv typing lifetime term expectedTy
            expectedEnv.toEnv := by
  intro hrefs hwell hmatches
  unfold checkTermMatches? at hmatches
  cases hcheck : checkTerm? fuel env typing lifetime term with
  | error message =>
      simp [hcheck] at hmatches
  | ok result =>
      simp [hcheck] at hmatches
      have htyping := checkTerm?_sound hrefs hwell hcheck
      have hmatch := checkResult_matches_sound hmatches
      rw [hmatch.1, hmatch.2] at htyping
      exact htyping

theorem termListTyping_of_checkTermListMatches? {fuel : Nat}
    {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
    {terms : List Term} {expectedTy : Ty} {expectedEnv : FiniteEnv} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
        checkTermListMatches? fuel env typing lifetime terms expectedTy
          expectedEnv = true →
          TermListTyping env.toEnv typing lifetime terms expectedTy
            expectedEnv.toEnv := by
  intro hrefs hwell hmatches
  unfold checkTermListMatches? at hmatches
  cases hcheck : checkTermList? fuel env typing lifetime terms with
  | error message =>
      simp [hcheck] at hmatches
  | ok result =>
      simp [hcheck] at hmatches
      have htyping := checkTermList?_sound hrefs hwell hcheck
      have hmatch := checkResult_matches_sound hmatches
      rw [hmatch.1, hmatch.2] at htyping
      exact htyping

theorem checkedTermTypingWitness_of_checkTermMatches? {fuel : Nat}
    {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {expectedTy : Ty} {expectedEnv : FiniteEnv} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
        checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv =
          true →
          CheckedTermTypingWitness fuel env typing lifetime term expectedTy
            expectedEnv := by
  intro hrefs hwell hmatches
  exact ⟨hmatches, termTyping_of_checkTermMatches? hrefs hwell hmatches⟩

theorem certifiedTermCheck_of_checkTermMatches? {fuel : Nat}
    {env : FiniteEnv} {typing : StoreTyping} {lifetime : Lifetime}
    {term : Term} {expectedTy : Ty} {expectedEnv : FiniteEnv} :
    (∀ env lifetime, StoreTypingRefsWellFormed env typing lifetime) →
      WellFormedEnv env.toEnv lifetime →
        checkTermMatches? fuel env typing lifetime term expectedTy expectedEnv =
          true →
          Nonempty
            (CertifiedTermCheck fuel env typing lifetime term expectedTy
              expectedEnv) := by
  intro hrefs hwell hmatches
  exact ⟨
    { checked := hmatches
      typing := termTyping_of_checkTermMatches? hrefs hwell hmatches }⟩

theorem checkProgram?_sound {fuel : Nat} {term : Term} {result : CheckResult} :
    checkProgram? fuel term = .ok result →
      TermTyping Env.empty StoreTyping.empty Lifetime.root term result.ty
        result.env.toEnv := by
  intro hcheck
  have hrefs :
      ∀ env lifetime,
        StoreTypingRefsWellFormed env StoreTyping.empty lifetime := by
    intro env lifetime
    exact storeTypingRefsWellFormed_empty env lifetime
  exact checkTerm?_sound
      (env := FiniteEnv.empty) (typing := StoreTyping.empty)
      (lifetime := Lifetime.root) (term := term) (result := result)
      hrefs
      (by
        simp [FiniteEnv.toEnv_empty, wellFormedEnv_empty])
      (by simpa [checkProgram?] using hcheck)

theorem termTyping_of_checkProgram?_matches {fuel : Nat} {term : Term}
    {result : CheckResult} {ty : Ty} {env : Env} :
    checkProgram? fuel term = .ok result →
      result.ty = ty →
        result.env.toEnv = env →
          TermTyping Env.empty StoreTyping.empty Lifetime.root term ty env := by
  intro hcheck hty henv
  have htyping := checkProgram?_sound hcheck
  rw [hty, henv] at htyping
  exact htyping

/--
Executable proof-carrying accepted checker.

When `checkProgram?` accepts, this returns the successful checker run packaged
with the corresponding declarative typing derivation.  When the checker returns
`.failed` or `.unknown`, no accepted-run certificate is produced.
-/
def certifyBorrowCheck? (fuel : Nat) (term : Term) :
    Option (CertifiedBorrowCheck fuel term) :=
  match hcheck : checkProgram? fuel term with
  | .ok result =>
      some
        { ty := result.ty
          env := result.env
          certificate :=
            { checked := by
                have hterm :
                    checkTerm? fuel FiniteEnv.empty StoreTyping.empty
                      Lifetime.root term = .ok result := by
                  simpa [checkProgram?] using hcheck
                unfold checkTermMatches? CheckResult.matches
                rw [hterm]
                simp [FiniteEnv.sameBindings_self]
              typing := by
                simpa [FiniteEnv.toEnv_empty] using checkProgram?_sound hcheck } }
  | .error _ => none

theorem certifyBorrowCheck?_found_iff {fuel : Nat} {term : Term} :
    CertifiedBorrowCheck.found? (certifyBorrowCheck? fuel term) = true ↔
      borrowCheck? fuel term = true := by
  unfold CertifiedBorrowCheck.found? certifyBorrowCheck? borrowCheck?
    borrowCheckVerdict?
  split
  · rename_i result hcheck
    simp [hcheck]
  · rename_i message hcheck
    cases hunknown : checkerErrorUnknown? message <;>
      simp [hcheck, hunknown]

/--
Proof-level reflection target for the executable accepted checker.

`borrowCheckWitness fuel term` means that the successful executable run has
been reified as a `CertifiedBorrowCheck`, i.e. as both a checker trace and the
corresponding inductive typing derivation.
-/
def borrowCheckWitness (fuel : Nat) (term : Term) : Prop :=
  Nonempty (CertifiedBorrowCheck fuel term)

theorem borrowCheck?_eq_true_iff_witness {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true ↔ borrowCheckWitness fuel term := by
  constructor
  · intro hcheck
    have hfound :
        CertifiedBorrowCheck.found? (certifyBorrowCheck? fuel term) = true :=
      (certifyBorrowCheck?_found_iff).2 hcheck
    unfold CertifiedBorrowCheck.found? at hfound
    cases hcert : certifyBorrowCheck? fuel term with
    | none =>
        simp [hcert] at hfound
    | some certificate =>
        exact ⟨certificate⟩
  · intro hwitness
    rcases hwitness with ⟨certificate⟩
    exact certificate.checked

theorem borrowCheck?_eq_false_iff_no_witness {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = false ↔ ¬ borrowCheckWitness fuel term := by
  constructor
  · intro hfalse hwitness
    have htrue := (borrowCheck?_eq_true_iff_witness).2 hwitness
    rw [hfalse] at htrue
    cases htrue
  · intro hnoWitness
    cases hcheck : borrowCheck? fuel term
    · rfl
    · exact False.elim
        (hnoWitness ((borrowCheck?_eq_true_iff_witness).1 hcheck))

theorem borrowCheckWitness_sound {fuel : Nat} {term : Term} :
    borrowCheckWitness fuel term → borrowCheck term := by
  intro hwitness
  rcases hwitness with ⟨certificate⟩
  exact certificate.borrowCheck

theorem borrowReject_no_borrowCheckWitness {fuel : Nat} {term : Term} :
    borrowReject term → ¬ borrowCheckWitness fuel term := by
  intro hreject hwitness
  exact hreject (borrowCheckWitness_sound hwitness)

theorem borrowReject_no_borrowCheckWitness_anyFuel {term : Term} :
    borrowReject term → ∀ fuel, ¬ borrowCheckWitness fuel term := by
  intro hreject fuel
  exact borrowReject_no_borrowCheckWitness (fuel := fuel) hreject

theorem borrowCheck?_eq_false_of_borrowReject {fuel : Nat} {term : Term} :
    borrowReject term → borrowCheck? fuel term = false := by
  intro hreject
  exact (borrowCheck?_eq_false_iff_no_witness).2
    (borrowReject_no_borrowCheckWitness (fuel := fuel) hreject)

theorem borrowCheckWitness_checked {fuel : Nat} {term : Term} :
    borrowCheckWitness fuel term → borrowCheck? fuel term = true := by
  intro hwitness
  exact (borrowCheck?_eq_true_iff_witness).2 hwitness

theorem borrowCheckFailureWitness_no_borrowCheckWitness
    {fuel : Nat} {term : Term} :
    borrowCheckFailureWitness fuel term →
      ¬ borrowCheckWitness fuel term := by
  intro hfailure haccepted
  have hfailed := borrowCheckFailureWitness_checked hfailure
  have hcheck := borrowCheckWitness_checked haccepted
  have hnotFailed := borrowCheckFailed?_false_of_borrowCheck? hcheck
  rw [hfailed] at hnotFailed
  cases hnotFailed

theorem borrowUnknownWitness_no_borrowCheckWitness
    {fuel : Nat} {term : Term} :
    borrowUnknownWitness fuel term →
      ¬ borrowCheckWitness fuel term := by
  intro hunknown haccepted
  have hunknownChecked := borrowUnknownWitness_checked hunknown
  have hcheck := borrowCheckWitness_checked haccepted
  have hnotUnknown := borrowUnknown?_false_of_borrowCheck? hcheck
  rw [hunknownChecked] at hnotUnknown
  cases hnotUnknown

theorem borrowCheck_of_certifyBorrowCheck? {fuel : Nat} {term : Term} :
    CertifiedBorrowCheck.found? (certifyBorrowCheck? fuel term) = true →
      borrowCheck term := by
  exact CertifiedBorrowCheck.borrowCheck_of_found?
    (certificate? := certifyBorrowCheck? fuel term)

theorem borrowCheck_of_borrowCheck? {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true → borrowCheck term := by
  exact borrowCheck_of_checkProgram?_sound
    (fun result hresult => checkProgram?_sound hresult)

theorem borrowCheck?_sound {fuel : Nat} {term : Term} :
    borrowCheck? fuel term = true → borrowCheck term :=
  borrowCheck_of_borrowCheck?

theorem borrowCheck_of_borrowCheckVerdict?_accepted {fuel : Nat} {term : Term} :
    borrowCheckVerdict? fuel term = .accepted → borrowCheck term := by
  intro hverdict
  exact borrowCheck?_sound (fuel := fuel) (term := term) (by
    simp [borrowCheck?, hverdict])

/--
Proof-carrying closed-program checker outcome.

An `accepted` outcome carries the executable successful run and its inductive
typing proof.  A `rejected` outcome carries both an executable failure and an
inductive no-typing proof.  Plain `.failed` checker verdicts are intentionally
not promoted to this type: they need a `CertifiedBorrowReject` witness first.
-/
inductive CertifiedBorrowOutcome (fuel : Nat) (term : Term) : Type where
  | accepted (certificate : CertifiedBorrowCheck fuel term)
  | rejected (certificate : CertifiedBorrowReject fuel term)

namespace CertifiedBorrowOutcome

def found? {fuel : Nat} {term : Term}
    (outcome? : Option (CertifiedBorrowOutcome fuel term)) : Bool :=
  outcome?.isSome

def certifyBorrowOutcome? (fuel : Nat) (term : Term)
    (rejection? : Option (CertifiedBorrowReject fuel term) := none) :
    Option (CertifiedBorrowOutcome fuel term) :=
  match certifyBorrowCheck? fuel term with
  | some certificate => some (.accepted certificate)
  | none =>
      match rejection? with
      | some certificate => some (.rejected certificate)
      | none => none

theorem sound {fuel : Nat} {term : Term}
    (outcome : CertifiedBorrowOutcome fuel term) :
    borrowCheck term ∨ borrowReject term := by
  cases outcome with
  | accepted certificate =>
      exact Or.inl certificate.borrowCheck
  | rejected certificate =>
      exact Or.inr certificate.borrowReject

theorem checked {fuel : Nat} {term : Term}
    (outcome : CertifiedBorrowOutcome fuel term) :
    borrowCheck? fuel term = true ∨ borrowCheckFailed? fuel term = true := by
  cases outcome with
  | accepted certificate =>
      exact Or.inl certificate.checked
  | rejected certificate =>
      exact Or.inr certificate.checkedFailure

theorem sound_of_found? {fuel : Nat} {term : Term}
    {outcome? : Option (CertifiedBorrowOutcome fuel term)} :
    found? outcome? = true → borrowCheck term ∨ borrowReject term := by
  cases outcome? with
  | none =>
      simp [found?]
  | some outcome =>
      intro _h
      exact outcome.sound

theorem checked_of_found? {fuel : Nat} {term : Term}
    {outcome? : Option (CertifiedBorrowOutcome fuel term)} :
    found? outcome? = true →
      borrowCheck? fuel term = true ∨ borrowCheckFailed? fuel term = true := by
  cases outcome? with
  | none =>
      simp [found?]
  | some outcome =>
      intro _h
      exact outcome.checked

theorem found_of_borrowCheck? {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowCheck? fuel term = true →
      found? (certifyBorrowOutcome? fuel term rejection?) = true := by
  intro hcheck
  have hcert :
      CertifiedBorrowCheck.found? (certifyBorrowCheck? fuel term) = true :=
    (certifyBorrowCheck?_found_iff).2 hcheck
  unfold found? certifyBorrowOutcome?
  cases hcertificate : certifyBorrowCheck? fuel term with
  | none =>
      have hnotFound :
          CertifiedBorrowCheck.found? (certifyBorrowCheck? fuel term) = false := by
        simp [CertifiedBorrowCheck.found?, hcertificate]
      rw [hnotFound] at hcert
      cases hcert
  | some certificate =>
      simp

theorem sound_of_certifyBorrowOutcome? {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    found? (certifyBorrowOutcome? fuel term rejection?) = true →
      borrowCheck term ∨ borrowReject term :=
  sound_of_found?

theorem checked_of_certifyBorrowOutcome? {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    found? (certifyBorrowOutcome? fuel term rejection?) = true →
      borrowCheck? fuel term = true ∨ borrowCheckFailed? fuel term = true :=
  checked_of_found?

end CertifiedBorrowOutcome

/--
Executable found/not-found bit for proof-carrying borrow-checking outcomes.

With no rejection certificate, this is the accepted-checker witness bit.  With a
`CertifiedBorrowReject`, it can also return true for a proof-carrying rejection.
Either way, `borrowOutcome?_sound` turns a true bit into an inductive fact.
-/
def borrowOutcome? (fuel : Nat) (term : Term)
    (rejection? : Option (CertifiedBorrowReject fuel term) := none) : Bool :=
  CertifiedBorrowOutcome.found?
    (CertifiedBorrowOutcome.certifyBorrowOutcome? fuel term rejection?)

/--
Proof-level reflection target for `borrowOutcome?`.

Unlike `CertifiedBorrowOutcome` by itself, this records that the executable
outcome function actually returned the witness, using the optional rejection
certificate supplied by the caller.
-/
def borrowOutcomeWitness (fuel : Nat) (term : Term)
    (rejection? : Option (CertifiedBorrowReject fuel term) := none) : Prop :=
  ∃ outcome,
    CertifiedBorrowOutcome.certifyBorrowOutcome? fuel term rejection? =
      some outcome

theorem borrowOutcome?_eq_true_iff_witness {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowOutcome? fuel term rejection? = true ↔
      borrowOutcomeWitness fuel term rejection? := by
  unfold borrowOutcome? borrowOutcomeWitness CertifiedBorrowOutcome.found?
  cases hcert :
      CertifiedBorrowOutcome.certifyBorrowOutcome? fuel term rejection? with
  | none =>
      simp
  | some outcome =>
      simp

theorem borrowOutcome?_eq_false_iff_no_witness {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowOutcome? fuel term rejection? = false ↔
      ¬ borrowOutcomeWitness fuel term rejection? := by
  constructor
  · intro hfalse hwitness
    have htrue := (borrowOutcome?_eq_true_iff_witness).2 hwitness
    rw [hfalse] at htrue
    cases htrue
  · intro hnoWitness
    cases hcheck : borrowOutcome? fuel term rejection?
    · rfl
    · exact False.elim
        (hnoWitness ((borrowOutcome?_eq_true_iff_witness).1 hcheck))

theorem borrowOutcomeWitness_sound {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowOutcomeWitness fuel term rejection? →
      borrowCheck term ∨ borrowReject term := by
  rintro ⟨outcome, _houtcome⟩
  exact outcome.sound

theorem borrowOutcomeWitness_checked {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowOutcomeWitness fuel term rejection? →
      borrowCheck? fuel term = true ∨ borrowCheckFailed? fuel term = true := by
  rintro ⟨outcome, _houtcome⟩
  exact outcome.checked

theorem borrowOutcome?_sound {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowOutcome? fuel term rejection? = true →
      borrowCheck term ∨ borrowReject term := by
  intro hfound
  exact CertifiedBorrowOutcome.sound_of_certifyBorrowOutcome?
    (rejection? := rejection?) (by simpa [borrowOutcome?] using hfound)

theorem borrowOutcome?_checked {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowOutcome? fuel term rejection? = true →
      borrowCheck? fuel term = true ∨ borrowCheckFailed? fuel term = true := by
  intro hfound
  exact CertifiedBorrowOutcome.checked_of_certifyBorrowOutcome?
    (rejection? := rejection?) (by simpa [borrowOutcome?] using hfound)

theorem borrowOutcome?_of_borrowCheck? {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)} :
    borrowCheck? fuel term = true → borrowOutcome? fuel term rejection? = true := by
  intro hcheck
  exact CertifiedBorrowOutcome.found_of_borrowCheck?
    (rejection? := rejection?) hcheck

theorem borrowOutcome?_of_certifiedCheck {fuel : Nat} {term : Term}
    {rejection? : Option (CertifiedBorrowReject fuel term)}
    (certificate : CertifiedBorrowCheck fuel term) :
    borrowOutcome? fuel term rejection? = true :=
  borrowOutcome?_of_borrowCheck? certificate.checked

theorem borrowOutcome?_of_certifiedReject {fuel : Nat} {term : Term}
    (certificate : CertifiedBorrowReject fuel term) :
    borrowOutcome? fuel term (some certificate) = true := by
  unfold borrowOutcome? CertifiedBorrowOutcome.found?
    CertifiedBorrowOutcome.certifyBorrowOutcome?
  cases certifyBorrowCheck? fuel term <;> simp

theorem borrowOutcome?_none_eq_true_iff {fuel : Nat} {term : Term} :
    borrowOutcome? fuel term = true ↔ borrowCheck? fuel term = true := by
  constructor
  · intro hfound
    unfold borrowOutcome? CertifiedBorrowOutcome.found?
      CertifiedBorrowOutcome.certifyBorrowOutcome? at hfound
    cases hcert : certifyBorrowCheck? fuel term with
    | none =>
        simp [hcert] at hfound
    | some certificate =>
        exact certificate.checked
  · exact borrowOutcome?_of_borrowCheck?

theorem borrowCheck_of_borrowOutcome? {fuel : Nat} {term : Term} :
    borrowOutcome? fuel term = true → borrowCheck term := by
  intro hfound
  exact borrowCheck?_sound ((borrowOutcome?_none_eq_true_iff).1 hfound)

theorem borrowCheck_of_borrowOutcomeWitness {fuel : Nat} {term : Term} :
    borrowOutcomeWitness fuel term → borrowCheck term := by
  intro hwitness
  exact borrowCheck_of_borrowOutcome?
    ((borrowOutcome?_eq_true_iff_witness).2 hwitness)

macro_rules
  | `(tactic| borrow_check using $certificate) =>
      `(tactic|
        first
        | exact LwRust.Paper.borrowOutcome?_of_certifiedCheck $certificate
        | exact LwRust.Paper.borrowOutcome?_of_certifiedReject $certificate
        | exact (LwRust.Paper.borrowCheck?_eq_true_iff_witness).1
            (LwRust.Paper.CertifiedBorrowCheck.checked $certificate)
        | exact (LwRust.Paper.borrowOutcome?_eq_true_iff_witness).1
            (LwRust.Paper.borrowOutcome?_of_certifiedCheck $certificate)
        | exact (LwRust.Paper.borrowOutcome?_eq_true_iff_witness).1
            (LwRust.Paper.borrowOutcome?_of_certifiedReject $certificate)
        | exact LwRust.Paper.CertifiedBorrowCheck.borrowCheck $certificate
        | exact LwRust.Paper.CertifiedBorrowCheck.checked $certificate
        | exact LwRust.Paper.CertifiedBorrowCheck.borrowCheck_of_found?
            (certificate? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedBorrowCheck.checked_of_found?
            (certificate? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedBorrowReject.borrowReject $certificate
        | exact LwRust.Paper.CertifiedBorrowReject.checkedFailure $certificate
        | exact LwRust.Paper.CertifiedBorrowReject.borrowReject_of_found?
            (certificate? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedBorrowReject.checkedFailure_of_found?
            (certificate? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedBorrowOutcome.sound $certificate
        | exact LwRust.Paper.CertifiedBorrowOutcome.checked $certificate
        | exact LwRust.Paper.CertifiedBorrowOutcome.sound_of_found?
            (outcome? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedBorrowOutcome.checked_of_found?
            (outcome? := $certificate) (by native_decide)
        | exact LwRust.Paper.CertifiedTermCheck.sound $certificate
        | exact LwRust.Paper.CertifiedTermCheck.toWitness $certificate
        | exact LwRust.Paper.CertifiedTermCheck.check_matches $certificate
        | exact LwRust.Paper.CertifiedTermCheck.typable $certificate
        | exact LwRust.Paper.CertifiedTermListCheck.sound $certificate
        | exact LwRust.Paper.CertifiedTermReject.sound $certificate
        | exact LwRust.Paper.CertifiedTermReject.checkedFailure $certificate
        | exact $certificate)

macro_rules
  | `(tactic| borrow_check[$fuel, $env, $expectedEnv]) =>
      `(tactic|
        first
        | exact LwRust.Paper.termTyping_of_checkTermMatches?
            (fuel := $fuel) (env := $env) (expectedEnv := $expectedEnv)
            (fun env lifetime =>
              LwRust.Paper.storeTypingRefsWellFormed_empty env lifetime)
            (by
              first
              | simp [LwRust.Paper.FiniteEnv.toEnv_empty,
                  LwRust.Paper.wellFormedEnv_empty]
              | native_decide)
            (by native_decide)
        | exact LwRust.Paper.termListTyping_of_checkTermListMatches?
            (fuel := $fuel) (env := $env) (expectedEnv := $expectedEnv)
            (fun env lifetime =>
              LwRust.Paper.storeTypingRefsWellFormed_empty env lifetime)
            (by
              first
              | simp [LwRust.Paper.FiniteEnv.toEnv_empty,
                  LwRust.Paper.wellFormedEnv_empty]
              | native_decide)
            (by native_decide))

macro_rules
  | `(tactic| borrow_check[$fuel, $result]) =>
      `(tactic|
        first
        | exact LwRust.Paper.termTyping_of_checkProgram?_matches
            (fuel := $fuel) (result := $result)
            (by native_decide) (by native_decide)
            (by simp [LwRust.Paper.FiniteEnv.toEnv_empty])
        | borrow_check[$fuel])

macro_rules
  | `(tactic| borrow_check[$fuel]) =>
      `(tactic|
        first
        | exact LwRust.Paper.borrowCheck_of_certifyBorrowCheck?
            (fuel := $fuel) (by native_decide)
        | exact LwRust.Paper.borrowCheck?_sound
            (fuel := $fuel) (by native_decide)
        | exact (LwRust.Paper.borrowCheck?_eq_true_iff_witness
            (fuel := $fuel)).1 (by native_decide)
        | exact (LwRust.Paper.borrowOutcome?_eq_true_iff_witness
            (fuel := $fuel)).1 (by native_decide)
        | exact LwRust.Paper.borrowCheckFailureWitness_of_certifyBorrowFailure?
            (fuel := $fuel) (by native_decide)
        | exact LwRust.Paper.borrowUnknownWitness_of_certifyBorrowUnknown?
            (fuel := $fuel) (by native_decide)
        | exact LwRust.Paper.borrowCheckFailureWitness_no_borrowCheckWitness
            ((LwRust.Paper.borrowCheckFailed?_eq_true_iff_witness
              (fuel := $fuel)).1 (by native_decide))
        | exact LwRust.Paper.borrowUnknownWitness_no_borrowCheckWitness
            ((LwRust.Paper.borrowUnknown?_eq_true_iff_witness
              (fuel := $fuel)).1 (by native_decide))
        | exact (LwRust.Paper.borrowCheck?_eq_false_iff_no_witness
            (fuel := $fuel)).1 (by native_decide)
        | exact (LwRust.Paper.borrowOutcome?_eq_false_iff_no_witness
            (fuel := $fuel)).1 (by native_decide)
        | borrow_run)

macro_rules
  | `(tactic| borrow_check) =>
      `(tactic|
        first
        | exact LwRust.Paper.borrowCheck_of_certifyBorrowCheck?
            (fuel := 256) (by native_decide)
        | exact LwRust.Paper.borrowCheck?_sound
            (fuel := 256) (by native_decide)
        | exact (LwRust.Paper.borrowCheck?_eq_true_iff_witness
            (fuel := 256)).1 (by native_decide)
        | exact (LwRust.Paper.borrowOutcome?_eq_true_iff_witness
            (fuel := 256)).1 (by native_decide)
        | exact LwRust.Paper.borrowCheckFailureWitness_of_certifyBorrowFailure?
            (fuel := 256) (by native_decide)
        | exact LwRust.Paper.borrowUnknownWitness_of_certifyBorrowUnknown?
            (fuel := 256) (by native_decide)
        | exact LwRust.Paper.borrowCheckFailureWitness_no_borrowCheckWitness
            ((LwRust.Paper.borrowCheckFailed?_eq_true_iff_witness
              (fuel := 256)).1 (by native_decide))
        | exact LwRust.Paper.borrowUnknownWitness_no_borrowCheckWitness
            ((LwRust.Paper.borrowUnknown?_eq_true_iff_witness
              (fuel := 256)).1 (by native_decide))
        | exact (LwRust.Paper.borrowCheck?_eq_false_iff_no_witness
            (fuel := 256)).1 (by native_decide)
        | exact (LwRust.Paper.borrowOutcome?_eq_false_iff_no_witness
            (fuel := 256)).1 (by native_decide)
        | borrow_run)

structure CertifiedLValFullType (fuel : Nat) (env : FiniteEnv)
    (lv : LVal) : Type where
  ty : Ty
  lifetime : Lifetime
  checked : lvalType? fuel env lv = some (.ty ty, lifetime)

namespace CertifiedLValFullType

theorem typing {fuel : Nat} {env : FiniteEnv} {lv : LVal}
    (certificate : CertifiedLValFullType fuel env lv) :
    LValTyping env.toEnv lv (.ty certificate.ty) certificate.lifetime :=
  lvalType?_sound certificate.checked

end CertifiedLValFullType

def certifyLValFullType? (fuel : Nat) (env : FiniteEnv) (lv : LVal) :
    Option (CertifiedLValFullType fuel env lv) :=
  match h : lvalType? fuel env lv with
  | some (.ty ty, lifetime) =>
      some { ty := ty, lifetime := lifetime, checked := h }
  | _ => none

namespace CertifiedTermCheck

def copyFromChecker {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    (lvalCert : CertifiedLValFullType fuel env lv)
    (checked :
      checkTermMatches? fuel env typing lifetime (.copy lv)
        lvalCert.ty env = true)
    (copyChecked : copyTy lvalCert.ty = true)
    (notReadChecked : readProhibited env lv = false) :
    CertifiedTermCheck fuel env typing lifetime (.copy lv) lvalCert.ty env :=
  { checked := by
      simpa using checked
    typing :=
      TermTyping.copy lvalCert.typing (copyTy_sound copyChecked)
        (readProhibited_false_sound notReadChecked) }

def copyFromCheckerAs {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    {expectedTy : Ty}
    (lvalCert : CertifiedLValFullType fuel env lv)
    (typeEq : lvalCert.ty = expectedTy)
    (checked :
      checkTermMatches? fuel env typing lifetime (.copy lv) expectedTy env =
        true)
    (copyChecked : copyTy expectedTy = true)
    (notReadChecked : readProhibited env lv = false) :
    CertifiedTermCheck fuel env typing lifetime (.copy lv) expectedTy env := by
  subst typeEq
  exact copyFromChecker lvalCert checked copyChecked notReadChecked

def mutBorrowFromChecker {fuel : Nat} {env : FiniteEnv}
    {typing : StoreTyping} {lifetime : Lifetime} {lv : LVal}
    (lvalCert : CertifiedLValFullType fuel env lv)
    (checked :
      checkTermMatches? fuel env typing lifetime (.borrow true lv)
        (.borrow true [lv]) env = true)
    (mutableChecked : mutableLVal fuel env lv = true)
    (notWriteChecked : writeProhibited env lv = false) :
    CertifiedTermCheck fuel env typing lifetime (.borrow true lv)
      (.borrow true [lv]) env :=
  { checked := checked
    typing :=
      TermTyping.mutBorrow lvalCert.typing
        (mutableLVal_sound mutableChecked)
        (writeProhibited_false_sound notWriteChecked) }

end CertifiedTermCheck

syntax (name := borrow_cert_tactic) "borrow_cert" : tactic

macro_rules
  | `(tactic| borrow_cert) =>
      `(tactic|
        first
        | exact CertifiedTermCheck.mutBorrowFromChecker
            ((certifyLValFullType? _ _ _).get (by native_decide))
            (by borrow_run)
            (by native_decide)
            (by native_decide)
        | exact CertifiedTermCheck.copyFromCheckerAs
            ((certifyLValFullType? _ _ _).get (by native_decide))
            (by native_decide)
            (by borrow_run)
            (by native_decide)
            (by native_decide))

end Paper
end LwRust
