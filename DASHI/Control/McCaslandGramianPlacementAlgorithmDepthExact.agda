module DASHI.Control.McCaslandGramianPlacementAlgorithmDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- William N. McCasland, Fault-Tolerant Sensor and Actuator Selection for Control
-- of Flexible Structures, 1989 ACC, pp. 1111-1116.
-- NASA index: norms of controllability/observability Gramians are performance
-- measures; algorithms include state-space scaling from a selected throughput path.

data PlacementRole : Set where sensor actuator : PlacementRole

data GramianKind : Set where controllability observability : GramianKind

data FailureMode : Set where noFailure singleSensorFailure singleActuatorFailure multipleFailure : FailureMode

record LinearPlacementModel : Set where
  constructor linear-placement-model
  field
    stateMatrix : String
    inputMatrix : String
    outputMatrix : String
    throughputPath : String
    scaledStateCoordinates : String
    sourceReference : String

open LinearPlacementModel public

record GramianPerformanceMetric : Set where
  constructor gramian-performance-metric
  field
    gramian : GramianKind
    definingRelation : String
    normOrScalarisation : String
    placementInterpretation : String

open GramianPerformanceMetric public

controllabilityMetric : GramianPerformanceMetric
controllabilityMetric = gramian-performance-metric
  controllability
  "A W_c + W_c A^T + B B^T = 0 for a stable continuous linear model"
  "source uses a selected norm on W_c"
  "rank candidate actuator sets by retained degree of controllability"

observabilityMetric : GramianPerformanceMetric
observabilityMetric = gramian-performance-metric
  observability
  "A^T W_o + W_o A + C^T C = 0 for a stable continuous linear model"
  "source uses a selected norm on W_o"
  "rank candidate sensor sets by retained degree of observability"

record FaultTolerantPlacementObjective : Set where
  constructor fault-tolerant-placement-objective
  field
    nominalMetric : String
    failureMetric : String
    redundancyConstraint : String
    reconfigurationRequirement : String
    algorithmReading : String

open FaultTolerantPlacementObjective public

canonicalFaultObjective : FaultTolerantPlacementObjective
canonicalFaultObjective = fault-tolerant-placement-objective
  "score the candidate placement in the intact plant"
  "recompute/reassess Gramian performance under specified component failures"
  "retain enough alternate sensing/actuation to preserve required control authority"
  "failed channel removal must route to an admissible surviving configuration"
  "McCasland 1989 develops placement algorithms for flexible structures with failures, using Gramian norms and throughput-path state scaling"

record McCaslandAlgorithmBoundary : Set where
  constructor mccasland-algorithm-boundary
  field
    nonsingularGramianMeansGoodFaultTolerance : Bool
    nonsingularGramianMeansGoodFaultToleranceIsFalse : nonsingularGramianMeansGoodFaultTolerance ≡ false
    nominalPlacementScoreOrdersEveryFailureCase : Bool
    nominalPlacementScoreOrdersEveryFailureCaseIsFalse : nominalPlacementScoreOrdersEveryFailureCase ≡ false
    coordinateScalingMayBeIgnoredWhenComparingGramianNorms : Bool
    coordinateScalingMayBeIgnoredWhenComparingGramianNormsIsFalse : coordinateScalingMayBeIgnoredWhenComparingGramianNorms ≡ false
    failureAwarePlacementNeedsExplicitFailureSet : Bool
    failureAwarePlacementNeedsExplicitFailureSetIsTrue : failureAwarePlacementNeedsExplicitFailureSet ≡ true

canonicalMcCaslandAlgorithmBoundary : McCaslandAlgorithmBoundary
canonicalMcCaslandAlgorithmBoundary = mccasland-algorithm-boundary false refl false refl false refl true refl

data McCaslandReverseTarget : Set where
  acquirePlantMatrices
  acquireThroughputPath
  acquireStateScaling
  acquireGramianNorm
  acquireCandidatePlacementSet
  acquireFailureSet
  acquireRedundancyConstraint
  acquireReconfigurationRule
  : McCaslandReverseTarget
