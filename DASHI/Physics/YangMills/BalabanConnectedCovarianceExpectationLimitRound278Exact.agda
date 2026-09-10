{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact where

------------------------------------------------------------------------
-- ROUND278 / SELECTED EXPECTATIONS -> CONNECTED-COVARIANCE MAGNITUDE LIMIT
--
-- R276 showed that canonical B1 needs only a one-sided finite upper plus
-- convergence to the exact spectral correlation.  The T5 expectation lane
-- already owns convergence of every selected bounded observable to the SAME
-- continuum measure.  Connected covariance therefore needs no separate
-- measure-limit theorem once the selected tests F, G and FG are present.
--
-- This file isolates the standard scalar-topology algebra:
--
--   E_n[FG] -> E[FG]
--   E_n[F]  -> E[F]
--   E_n[G]  -> E[G]
--
-- implies
--
--   | E_n[FG] - E_n[F] E_n[G] |
--       ->
--   | E[FG] - E[F] E[G] |.
--
-- Multiplication, negation and magnitude continuity are explicit authority
-- fields; they are not inferred from an opaque word such as "real".
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram

record ScalarCovarianceConvergenceExtension
    {Measure Observable Scalar : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable Scalar)
    : Set₁ where
  field
    negate magnitude : Scalar → Scalar

    multiplyConverges :
      (firstSequence secondSequence : Nat → Scalar)
      (firstLimit secondLimit : Scalar) →
      Gram.Converges (Gram.scalarConvergence dataSet)
        firstSequence firstLimit →
      Gram.Converges (Gram.scalarConvergence dataSet)
        secondSequence secondLimit →
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff →
          Gram.multiply (Gram.operations dataSet)
            (firstSequence cutoff) (secondSequence cutoff))
        (Gram.multiply (Gram.operations dataSet) firstLimit secondLimit)

    negateConverges :
      (sequence : Nat → Scalar) (limit : Scalar) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence limit →
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff → negate (sequence cutoff))
        (negate limit)

    magnitudeConverges :
      (sequence : Nat → Scalar) (limit : Scalar) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence limit →
      Gram.Converges (Gram.scalarConvergence dataSet)
        (λ cutoff → magnitude (sequence cutoff))
        (magnitude limit)

open ScalarCovarianceConvergenceExtension public

connectedCovarianceValue :
  ∀ {Measure Observable Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable Scalar} →
  ScalarCovarianceConvergenceExtension dataSet →
  Measure → Observable → Observable → Scalar
connectedCovarianceValue {dataSet = dataSet} extension measure left right =
  Gram.add (Gram.operations dataSet)
    (Gram.expectation (Gram.operations dataSet) measure
      (Gram.multiplyObservable (Gram.operations dataSet) left right))
    (negate extension
      (Gram.multiply (Gram.operations dataSet)
        (Gram.expectation (Gram.operations dataSet) measure left)
        (Gram.expectation (Gram.operations dataSet) measure right)))

connectedCovarianceMagnitude :
  ∀ {Measure Observable Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable Scalar} →
  ScalarCovarianceConvergenceExtension dataSet →
  Measure → Observable → Observable → Scalar
connectedCovarianceMagnitude extension measure left right =
  magnitude extension (connectedCovarianceValue extension measure left right)

record SelectedConnectedCovarianceTests
    {Measure Observable Scalar : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable Scalar)
    : Set₁ where
  field
    Index : Set
    left right : Index → Observable

    leftBounded : ∀ index →
      Gram.BoundedObservable dataSet (left index)
    rightBounded : ∀ index →
      Gram.BoundedObservable dataSet (right index)
    productBounded : ∀ index →
      Gram.BoundedObservable dataSet
        (Gram.multiplyObservable (Gram.operations dataSet)
          (left index) (right index))

open SelectedConnectedCovarianceTests public

selectedExpectationConverges :
  ∀ {Measure Observable Scalar}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable Scalar)
    observable →
  Gram.BoundedObservable dataSet observable →
  Gram.Converges (Gram.scalarConvergence dataSet)
    (λ cutoff →
      Gram.expectation (Gram.operations dataSet)
        (Gram.measureSequence dataSet cutoff) observable)
    (Gram.expectation (Gram.operations dataSet)
      (Gram.continuumMeasure dataSet) observable)
selectedExpectationConverges dataSet observable bounded =
  Gram.boundedWeakConvergenceImpliesExpectationConvergence
    dataSet observable bounded

selectedConnectedCovarianceConverges :
  ∀ {Measure Observable Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable Scalar}
    (extension : ScalarCovarianceConvergenceExtension dataSet)
    (tests : SelectedConnectedCovarianceTests dataSet)
    (index : Index tests) →
  Gram.Converges (Gram.scalarConvergence dataSet)
    (λ cutoff →
      connectedCovarianceValue extension
        (Gram.measureSequence dataSet cutoff)
        (left tests index) (right tests index))
    (connectedCovarianceValue extension
      (Gram.continuumMeasure dataSet)
      (left tests index) (right tests index))
selectedConnectedCovarianceConverges
    {dataSet = dataSet} extension tests index =
  let
    operations = Gram.operations dataSet
    leftObservable = left tests index
    rightObservable = right tests index
    productObservable =
      Gram.multiplyObservable operations leftObservable rightObservable

    productExpectationSequence = λ cutoff →
      Gram.expectation operations
        (Gram.measureSequence dataSet cutoff) productObservable
    productExpectationLimit =
      Gram.expectation operations (Gram.continuumMeasure dataSet) productObservable

    leftExpectationSequence = λ cutoff →
      Gram.expectation operations
        (Gram.measureSequence dataSet cutoff) leftObservable
    leftExpectationLimit =
      Gram.expectation operations (Gram.continuumMeasure dataSet) leftObservable

    rightExpectationSequence = λ cutoff →
      Gram.expectation operations
        (Gram.measureSequence dataSet cutoff) rightObservable
    rightExpectationLimit =
      Gram.expectation operations (Gram.continuumMeasure dataSet) rightObservable

    productObservableConverges =
      selectedExpectationConverges dataSet productObservable
        (productBounded tests index)
    leftConverges =
      selectedExpectationConverges dataSet leftObservable (leftBounded tests index)
    rightConverges =
      selectedExpectationConverges dataSet rightObservable (rightBounded tests index)

    productOfMeansConverges =
      multiplyConverges extension
        leftExpectationSequence rightExpectationSequence
        leftExpectationLimit rightExpectationLimit
        leftConverges rightConverges

    negativeProductOfMeansConverges =
      negateConverges extension
        (λ cutoff →
          Gram.multiply operations
            (leftExpectationSequence cutoff)
            (rightExpectationSequence cutoff))
        (Gram.multiply operations leftExpectationLimit rightExpectationLimit)
        productOfMeansConverges
  in
  Gram.addConverges (Gram.scalarConvergence dataSet)
    productExpectationSequence productExpectationLimit
    (λ cutoff →
      negate extension
        (Gram.multiply operations
          (leftExpectationSequence cutoff)
          (rightExpectationSequence cutoff)))
    (negate extension
      (Gram.multiply operations leftExpectationLimit rightExpectationLimit))
    productObservableConverges
    negativeProductOfMeansConverges

selectedConnectedCovarianceMagnitudeConverges :
  ∀ {Measure Observable Scalar}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable Scalar}
    (extension : ScalarCovarianceConvergenceExtension dataSet)
    (tests : SelectedConnectedCovarianceTests dataSet)
    (index : Index tests) →
  Gram.Converges (Gram.scalarConvergence dataSet)
    (λ cutoff →
      connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        (left tests index) (right tests index))
    (connectedCovarianceMagnitude extension
      (Gram.continuumMeasure dataSet)
      (left tests index) (right tests index))
selectedConnectedCovarianceMagnitudeConverges
    extension tests index =
  magnitudeConverges extension
    (λ cutoff →
      connectedCovarianceValue extension
        (Gram.measureSequence _ cutoff)
        (left tests index) (right tests index))
    (connectedCovarianceValue extension
      (Gram.continuumMeasure _)
      (left tests index) (right tests index))
    (selectedConnectedCovarianceConverges extension tests index)

record Round278Boundary : Set where
  constructor round278-boundary
  field
    separateCovarianceMeasureLimitRequired : Bool
    separateCovarianceMeasureLimitRequiredIsFalse :
      separateCovarianceMeasureLimitRequired ≡ false

    exactFiniteContinuumCovarianceEqualityRequired : Bool
    exactFiniteContinuumCovarianceEqualityRequiredIsFalse :
      exactFiniteContinuumCovarianceEqualityRequired ≡ false

    selectedLeftRightProductMeaningRequired : Bool
    selectedLeftRightProductMeaningRequiredIsTrue :
      selectedLeftRightProductMeaningRequired ≡ true

canonicalRound278Boundary : Round278Boundary
canonicalRound278Boundary =
  round278-boundary false refl false refl true refl

round278ConnectedCovarianceLimitCompilerLevel : ProofLevel
round278ConnectedCovarianceLimitCompilerLevel = machineChecked

round278ScalarRingAndMagnitudeContinuityLevel : ProofLevel
round278ScalarRingAndMagnitudeContinuityLevel = standardImported

round278SelectedCovarianceTestMeaningLevel : ProofLevel
round278SelectedCovarianceTestMeaningLevel = conditional
