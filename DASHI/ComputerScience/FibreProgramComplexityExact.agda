module DASHI.ComputerScience.FibreProgramComplexityExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- FIBRE-INDEXED PROGRAM COMPLEXITY
--
-- Program complexity is not collapsed to a single scalar.  A computation can
-- have distinct description, execution, storage, representation, trace, and
-- residual/provenance costs.  Which coordinates matter is consumer-indexed.
------------------------------------------------------------------------

record ComplexityProfile : Set where
  constructor complexityProfile
  field
    sourceDescriptionCost : Nat
    programStorageCost : Nat
    dataStorageCost : Nat
    executionStepCost : Nat
    registerStateCost : Nat
    representationCellCost : Nat
    traceCost : Nat
    residualWitnessCost : Nat

open ComplexityProfile public

record ComplexityConsumer : Set₁ where
  constructor complexityConsumer
  field
    Outcome : Set
    observeComplexity : ComplexityProfile → Outcome

open ComplexityConsumer public

sourceDescriptionConsumer : ComplexityConsumer
sourceDescriptionConsumer =
  complexityConsumer Nat sourceDescriptionCost

executionStepConsumer : ComplexityConsumer
executionStepConsumer =
  complexityConsumer Nat executionStepCost

representationCellConsumer : ComplexityConsumer
representationCellConsumer =
  complexityConsumer Nat representationCellCost

record FibreComplexityBoundary : Set where
  constructor fibreComplexityBoundary
  field
    oneScalarIsCanonicalForEveryConsumer : Bool
    executionCostEqualsDescriptionCost : Bool
    representationCostEqualsSemanticCost : Bool
    residualProvenanceCanBeTrackedSeparately : Bool
    complexityIsConsumerIndexed : Bool

canonicalFibreComplexityBoundary : FibreComplexityBoundary
canonicalFibreComplexityBoundary =
  fibreComplexityBoundary false false false true true
