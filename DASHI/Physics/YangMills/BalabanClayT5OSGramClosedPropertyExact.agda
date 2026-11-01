module DASHI.Physics.YangMills.BalabanClayT5OSGramClosedPropertyExact where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit

------------------------------------------------------------------------
-- Strong-topology adapter for the Osterwalder--Schrader positivity axiom.
--
-- K. Osterwalder and R. Schrader,
-- "Axioms for Euclidean Green's functions",
-- DOI: 10.1007/BF01645738
--
-- K. Osterwalder and R. Schrader,
-- "Axioms for Euclidean Green's functions II",
-- DOI: 10.1007/BF01608978
--
-- The old generic field `reflectionPositiveClosed` is now constructible from a
-- precise theorem: convergence of measures must imply convergence of every
-- complete reflected Gram quadratic form, and the scalar nonnegative cone must
-- be closed in that topology.
------------------------------------------------------------------------

record MeasureTopologyControlsOSGram
    (Measure Schwinger TestFamily Scalar : Set) : Set₁ where
  field
    measureLimit : Limit.SequentialLimit Measure
    scalarLimit : Limit.SequentialLimit Scalar

    schwinger : Measure → Schwinger
    reflectedGramQuadraticForm : Schwinger → TestFamily → Scalar
    Nonnegative : Scalar → Set

    measureConvergenceImpliesGramConvergence :
      ∀ sequence target →
      Limit.Converges measureLimit sequence target →
      ∀ testFamily →
      Limit.Converges scalarLimit
        (λ cutoff → reflectedGramQuadraticForm
          (schwinger (sequence cutoff)) testFamily)
        (reflectedGramQuadraticForm (schwinger target) testFamily)

    nonnegativeConeClosed : ∀ sequence target →
      Limit.Converges scalarLimit sequence target →
      (∀ cutoff → Nonnegative (sequence cutoff)) →
      Nonnegative target

open MeasureTopologyControlsOSGram public

MeasureReflectionPositive :
  ∀ {Measure Schwinger TestFamily Scalar} →
  MeasureTopologyControlsOSGram Measure Schwinger TestFamily Scalar →
  Measure → Set
MeasureReflectionPositive dataSet measure = ∀ testFamily →
  Nonnegative dataSet
    (reflectedGramQuadraticForm dataSet
      (schwinger dataSet measure) testFamily)

measureReflectionPositiveClosed :
  ∀ {Measure Schwinger TestFamily Scalar}
    (dataSet : MeasureTopologyControlsOSGram
      Measure Schwinger TestFamily Scalar)
    sequence target →
  Limit.Converges (measureLimit dataSet) sequence target →
  (∀ cutoff → MeasureReflectionPositive dataSet (sequence cutoff)) →
  MeasureReflectionPositive dataSet target
measureReflectionPositiveClosed dataSet sequence target converges pointwise testFamily =
  nonnegativeConeClosed dataSet
    (λ cutoff → reflectedGramQuadraticForm dataSet
      (schwinger dataSet (sequence cutoff)) testFamily)
    (reflectedGramQuadraticForm dataSet
      (schwinger dataSet target) testFamily)
    (measureConvergenceImpliesGramConvergence dataSet
      sequence target converges testFamily)
    (λ cutoff → pointwise cutoff testFamily)

reflectionPositiveSequentiallyClosed :
  ∀ {Measure Schwinger TestFamily Scalar}
    (dataSet : MeasureTopologyControlsOSGram
      Measure Schwinger TestFamily Scalar) →
  Limit.SequentiallyClosedProperty Measure
    (MeasureReflectionPositive dataSet)
reflectionPositiveSequentiallyClosed dataSet = record
  { limits = measureLimit dataSet
  ; closedUnderLimit =
      measureReflectionPositiveClosed dataSet
  }

osMeasureToGramContinuityLevel : ProofLevel
osMeasureToGramContinuityLevel = machineChecked

osReflectionPositiveClosedPropertyLevel : ProofLevel
osReflectionPositiveClosedPropertyLevel = machineChecked

-- The physical continuum theorem must establish the measure-to-Gram continuity
-- premise for the Wilson Schwinger functions.  Bare pointwise convergence of
-- correlators does not instantiate this record.
physicalMeasureToOSGramContinuityLevel : ProofLevel
physicalMeasureToOSGramContinuityLevel = conditional
