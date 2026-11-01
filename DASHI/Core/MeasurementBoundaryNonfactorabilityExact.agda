module DASHI.Core.MeasurementBoundaryNonfactorabilityExact where

------------------------------------------------------------------------
-- MEASUREMENT-BOUNDARY NONFACTORABILITY
--
-- A measurement can be perfectly well-defined for one purpose while erasing
-- distinctions needed by another consumer.  The generic theorem is deliberately
-- source-neutral; feminist-economics and safe/just modules instantiate it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer

record MeasurementBoundary (State Measured Material : Set) : Set₁ where
  constructor measurementBoundary
  field
    measure : State → Measured
    materialConsumer : State → Material

open MeasurementBoundary public

record BoundaryLossWitness
    {State Measured Material : Set}
    (boundary : MeasurementBoundary State Measured Material) : Set where
  constructor boundaryLossWitness
  field
    left right : State
    sameMeasured : measure boundary left ≡ measure boundary right
    differentMaterial : materialConsumer boundary left ≡ materialConsumer boundary right → ⊥

open BoundaryLossWitness public

boundaryLossGivesConsumerNonDescent :
  ∀ {State Measured Material : Set}
    {boundary : MeasurementBoundary State Measured Material} →
  BoundaryLossWitness boundary →
  Consumer.ConsumerNonDescentWitness
    (measure boundary)
    (materialConsumer boundary)
boundaryLossGivesConsumerNonDescent witness =
  Consumer.consumerNonDescentWitness
    (left witness)
    (right witness)
    (sameMeasured witness)
    (differentMaterial witness)

boundaryLossBlocksFactorization :
  ∀ {State Measured Material : Set}
    {boundary : MeasurementBoundary State Measured Material} →
  BoundaryLossWitness boundary →
  Consumer.FactorsThrough
    (measure boundary)
    (materialConsumer boundary) → ⊥
boundaryLossBlocksFactorization witness =
  Consumer.nonDescentWitnessBlocksFactorization
    (boundaryLossGivesConsumerNonDescent witness)

record MeasurementBoundaryPrinciple : Set where
  constructor measurementBoundaryPrinciple
  field
    validMeasurementImpliesConsumerCompleteness : Bool
    validMeasurementImpliesConsumerCompletenessIsFalse :
      validMeasurementImpliesConsumerCompleteness ≡ false
    equalMeasuredValueImpliesEqualMaterialContribution : Bool
    equalMeasuredValueImpliesEqualMaterialContributionIsFalse :
      equalMeasuredValueImpliesEqualMaterialContribution ≡ false
    erasedCoordinateCanBeRecoveredByRelabellingMeasurement : Bool
    erasedCoordinateCanBeRecoveredByRelabellingMeasurementIsFalse :
      erasedCoordinateCanBeRecoveredByRelabellingMeasurement ≡ false

canonicalMeasurementBoundaryPrinciple : MeasurementBoundaryPrinciple
canonicalMeasurementBoundaryPrinciple =
  measurementBoundaryPrinciple false refl false refl false refl
