{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5DirectExpectationPropertyClosureExact where

------------------------------------------------------------------------
-- SELECTED EXPECTATION CONVERGENCE -> CONTINUUM MEASURE PROPERTIES
--
-- The preferred T5 expectation producer already owns one continuum measure and
-- tail-controlled convergence of bounded selected-diagonal expectations to that
-- exact target.  Normalization, positivity and action invariance therefore do
-- not require a separate weak-convergence theorem for measures: they close at
-- the scalar-expectation level once the relevant observables belong to the
-- producer's bounded test class.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5

record ScalarExpectationClosureAuthority
    {Measure Observable Scalar : Set}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar) : Set₁ where
  field
    scalarConvergenceCongruent :
      (first second : Nat → Scalar) → (target : Scalar) →
      (∀ n → first n ≡ second n) →
      Gram.Converges (T5.scalarConvergence (T5.thermodynamic expectationData))
        first target →
      Gram.Converges (T5.scalarConvergence (T5.thermodynamic expectationData))
        second target

    scalarLimitUnique :
      (sequence : Nat → Scalar) → (first second : Scalar) →
      Gram.Converges (T5.scalarConvergence (T5.thermodynamic expectationData))
        sequence first →
      Gram.Converges (T5.scalarConvergence (T5.thermodynamic expectationData))
        sequence second →
      first ≡ second

    Nonnegative : Scalar → Set

    nonnegativeClosed :
      (sequence : Nat → Scalar) → (target : Scalar) →
      Gram.Converges (T5.scalarConvergence (T5.thermodynamic expectationData))
        sequence target →
      (∀ n → Nonnegative (sequence n)) →
      Nonnegative target

open ScalarExpectationClosureAuthority public

record SelectedExpectationPropertySemantics
    {Measure Observable Scalar : Set}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar)
    (scalarAuthority : ScalarExpectationClosureAuthority expectationData)
    (Action : Set) : Set₁ where
  field
    unitObservable : Observable
    one : Scalar

    unitObservableBounded :
      T5.BoundedObservable (T5.thermodynamic expectationData) unitObservable

    finiteUnitExpectation : ∀ cutoff →
      Gram.expectation (T5.operations (T5.thermodynamic expectationData))
        (T5.diagonalMeasure expectationData cutoff) unitObservable
      ≡ one

    PositiveObservable : Observable → Set

    positiveObservableBounded : ∀ observable →
      PositiveObservable observable →
      T5.BoundedObservable (T5.thermodynamic expectationData) observable

    finitePositiveExpectation : ∀ cutoff observable →
      PositiveObservable observable →
      Nonnegative scalarAuthority
        (Gram.expectation (T5.operations (T5.thermodynamic expectationData))
          (T5.diagonalMeasure expectationData cutoff) observable)

    act : Action → Observable → Observable
    ActionObservable : Observable → Set

    actionObservableBounded : ∀ observable →
      ActionObservable observable →
      T5.BoundedObservable (T5.thermodynamic expectationData) observable

    transformedActionObservableBounded : ∀ action observable →
      ActionObservable observable →
      T5.BoundedObservable (T5.thermodynamic expectationData)
        (act action observable)

    finiteActionInvariant : ∀ cutoff action observable →
      ActionObservable observable →
      Gram.expectation (T5.operations (T5.thermodynamic expectationData))
        (T5.diagonalMeasure expectationData cutoff) (act action observable)
      ≡ Gram.expectation (T5.operations (T5.thermodynamic expectationData))
        (T5.diagonalMeasure expectationData cutoff) observable

open SelectedExpectationPropertySemantics public

continuumExpectation :
  ∀ {Measure Observable Scalar}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar) →
  Observable → Scalar
continuumExpectation expectationData observable =
  Gram.expectation (T5.operations (T5.thermodynamic expectationData))
    (T5.continuumMeasure (T5.thermodynamic expectationData)) observable

boundedSelectedExpectationConverges :
  ∀ {Measure Observable Scalar}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar)
    (observable : Observable) →
  T5.BoundedObservable (T5.thermodynamic expectationData) observable →
  Gram.Converges (T5.scalarConvergence (T5.thermodynamic expectationData))
    (λ cutoff →
      Gram.expectation (T5.operations (T5.thermodynamic expectationData))
        (T5.diagonalMeasure expectationData cutoff) observable)
    (continuumExpectation expectationData observable)
boundedSelectedExpectationConverges = T5.boundedWeakConvergenceFromTail

ContinuumNormalized :
  ∀ {Measure Observable Scalar Action}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {scalarAuthority : ScalarExpectationClosureAuthority expectationData} →
  SelectedExpectationPropertySemantics expectationData scalarAuthority Action → Set
ContinuumNormalized {expectationData = expectationData} semantics =
  continuumExpectation expectationData (unitObservable semantics)
  ≡ one semantics

ContinuumPositive :
  ∀ {Measure Observable Scalar Action}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {scalarAuthority : ScalarExpectationClosureAuthority expectationData} →
  SelectedExpectationPropertySemantics expectationData scalarAuthority Action → Set
ContinuumPositive {expectationData = expectationData}
  {scalarAuthority = scalarAuthority} semantics =
  ∀ observable → PositiveObservable semantics observable →
  Nonnegative scalarAuthority (continuumExpectation expectationData observable)

ContinuumActionInvariant :
  ∀ {Measure Observable Scalar Action}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {scalarAuthority : ScalarExpectationClosureAuthority expectationData} →
  SelectedExpectationPropertySemantics expectationData scalarAuthority Action → Set
ContinuumActionInvariant {expectationData = expectationData} semantics =
  ∀ action observable → ActionObservable semantics observable →
  continuumExpectation expectationData (act semantics action observable)
  ≡ continuumExpectation expectationData observable

continuumNormalizedFromSelectedExpectations :
  ∀ {Measure Observable Scalar Action}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {scalarAuthority : ScalarExpectationClosureAuthority expectationData}
    (semantics :
      SelectedExpectationPropertySemantics
        expectationData scalarAuthority Action) →
  ContinuumNormalized semantics
continuumNormalizedFromSelectedExpectations
  {expectationData = expectationData}
  {scalarAuthority = scalarAuthority} semantics =
  scalarLimitUnique scalarAuthority
    (λ cutoff →
      Gram.expectation (T5.operations (T5.thermodynamic expectationData))
        (T5.diagonalMeasure expectationData cutoff)
        (unitObservable semantics))
    (continuumExpectation expectationData (unitObservable semantics))
    (one semantics)
    (boundedSelectedExpectationConverges expectationData
      (unitObservable semantics) (unitObservableBounded semantics))
    (scalarConvergenceCongruent scalarAuthority
      (λ _ → one semantics)
      (λ cutoff →
        Gram.expectation (T5.operations (T5.thermodynamic expectationData))
          (T5.diagonalMeasure expectationData cutoff)
          (unitObservable semantics))
      (one semantics)
      (λ cutoff → sym (finiteUnitExpectation semantics cutoff))
      (Gram.constantConverges
        (T5.scalarConvergence (T5.thermodynamic expectationData))
        (one semantics)))

continuumPositiveFromSelectedExpectations :
  ∀ {Measure Observable Scalar Action}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {scalarAuthority : ScalarExpectationClosureAuthority expectationData}
    (semantics :
      SelectedExpectationPropertySemantics
        expectationData scalarAuthority Action) →
  ContinuumPositive semantics
continuumPositiveFromSelectedExpectations
  {expectationData = expectationData}
  {scalarAuthority = scalarAuthority} semantics observable positive =
  nonnegativeClosed scalarAuthority
    (λ cutoff →
      Gram.expectation (T5.operations (T5.thermodynamic expectationData))
        (T5.diagonalMeasure expectationData cutoff) observable)
    (continuumExpectation expectationData observable)
    (boundedSelectedExpectationConverges expectationData observable
      (positiveObservableBounded semantics observable positive))
    (λ cutoff → finitePositiveExpectation semantics cutoff observable positive)

continuumActionInvariantFromSelectedExpectations :
  ∀ {Measure Observable Scalar Action}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {scalarAuthority : ScalarExpectationClosureAuthority expectationData}
    (semantics :
      SelectedExpectationPropertySemantics
        expectationData scalarAuthority Action) →
  ContinuumActionInvariant semantics
continuumActionInvariantFromSelectedExpectations
  {expectationData = expectationData}
  {scalarAuthority = scalarAuthority} semantics action observable admissible =
  scalarLimitUnique scalarAuthority
    (λ cutoff →
      Gram.expectation (T5.operations (T5.thermodynamic expectationData))
        (T5.diagonalMeasure expectationData cutoff)
        (act semantics action observable))
    (continuumExpectation expectationData (act semantics action observable))
    (continuumExpectation expectationData observable)
    (boundedSelectedExpectationConverges expectationData
      (act semantics action observable)
      (transformedActionObservableBounded semantics action observable admissible))
    (scalarConvergenceCongruent scalarAuthority
      (λ cutoff →
        Gram.expectation (T5.operations (T5.thermodynamic expectationData))
          (T5.diagonalMeasure expectationData cutoff) observable)
      (λ cutoff →
        Gram.expectation (T5.operations (T5.thermodynamic expectationData))
          (T5.diagonalMeasure expectationData cutoff)
          (act semantics action observable))
      (continuumExpectation expectationData observable)
      (λ cutoff → sym
        (finiteActionInvariant semantics cutoff action observable admissible))
      (boundedSelectedExpectationConverges expectationData observable
        (actionObservableBounded semantics observable admissible)))

directExpectationPropertyClosureCompilerLevel : ProofLevel
directExpectationPropertyClosureCompilerLevel = machineChecked

scalarExpectationHausdorffAndConeAuthorityLevel : ProofLevel
scalarExpectationHausdorffAndConeAuthorityLevel = standardImported

-- Physical representation seam: the unit, positive and action observables used
-- by the continuum consumer must be the bounded selected tests whose finite
-- expectation identities are actually owned by the cutoff theory.
selectedExpectationPropertySemanticsLevel : ProofLevel
selectedExpectationPropertySemanticsLevel = conditional
