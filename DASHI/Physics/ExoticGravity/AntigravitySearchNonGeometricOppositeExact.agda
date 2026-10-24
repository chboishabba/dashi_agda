module DASHI.Physics.ExoticGravity.AntigravitySearchNonGeometricOppositeExact where

open import DASHI.Core.Prelude

import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as ArgumentOpposite
import DASHI.Physics.GR.ControlledEMGWEinsteinCouplingDegeneracyExact as FixedMetric

------------------------------------------------------------------------
-- ANTIGRAVITY SEARCH: SIGN OPPOSITE != GEOMETRIC OPPOSITE
--
-- Cross-pollination donor:
--   DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact
--
-- That module proves that an adversarial/response-side opposite does not
-- construct the geometric antipode of the original object.  The gravity
-- analogue is the same structural warning: changing a label or coupling sign
-- is a search-space transformation.  A geometric antipode must be obtained by
-- re-solving the physical model and proving that the resulting metric/field is
-- the required opposite object.
------------------------------------------------------------------------

argumentResponseDonorBoundary :
  ArgumentOpposite.ArgumentResponseGeometryBoundary
argumentResponseDonorBoundary =
  ArgumentOpposite.canonicalArgumentResponseGeometryBoundary

fixedMetricDegeneracyBoundary :
  FixedMetric.ControlledExchangeSignedGBoundary
fixedMetricDegeneracyBoundary =
  FixedMetric.canonicalControlledExchangeSignedGBoundary

data AntigravitySearchTransform : Set where
  couplingSignFlip : AntigravitySearchTransform
  sourceSignFlip : AntigravitySearchTransform
  constitutiveSignFlip : AntigravitySearchTransform
  metricAntipodeRequest : AntigravitySearchTransform
  accelerationAntipodeRequest : AntigravitySearchTransform

data GeometricTarget : Set where
  metricSolutionTarget : GeometricTarget
  connectionTarget : GeometricTarget
  curvatureTarget : GeometricTarget
  geodesicAccelerationTarget : GeometricTarget
  clockRedshiftTarget : GeometricTarget

record AntigravitySearchState : Set₁ where
  constructor antigravity-search-state
  field
    CouplingParameter : Set
    SourceState : Set
    MetricSolution : Set
    ObservablePrediction : Set

    coupling : CouplingParameter
    source : SourceState
    metric : MetricSolution
    observable : ObservablePrediction

    solveMetric : CouplingParameter → SourceState → MetricSolution
    projectObservable : MetricSolution → ObservablePrediction

open AntigravitySearchState public

record GeometricOppositeReceipt (state : AntigravitySearchState) : Set₁ where
  constructor geometric-opposite-receipt
  field
    oppositeCoupling : CouplingParameter state
    oppositeSource : SourceState state
    resolvedMetric : MetricSolution state

    resolvedMetricIsSolvedObject :
      resolvedMetric ≡ solveMetric state oppositeCoupling oppositeSource

    GeometricOppositePredicate :
      MetricSolution state → MetricSolution state → Set

    resolvedMetricIsGeometricOpposite :
      GeometricOppositePredicate (metric state) resolvedMetric

open GeometricOppositeReceipt public

------------------------------------------------------------------------
-- Empty automatic-promotion propositions.
------------------------------------------------------------------------

data CouplingSignFlipAutomaticallyConstructsMetricAntipode : Set where
data FixedMetricSignedCouplingRelabelIsPhysicalAntipode : Set where
data OppositeSearchRoleAutomaticallyReversesAccelerationField : Set where

couplingSignFlipDoesNotAutomaticallyConstructMetricAntipode :
  CouplingSignFlipAutomaticallyConstructsMetricAntipode → ⊥
couplingSignFlipDoesNotAutomaticallyConstructMetricAntipode ()

fixedMetricRelabelIsNotPhysicalAntipode :
  FixedMetricSignedCouplingRelabelIsPhysicalAntipode → ⊥
fixedMetricRelabelIsNotPhysicalAntipode ()

oppositeSearchRoleDoesNotAutomaticallyReverseAcceleration :
  OppositeSearchRoleAutomaticallyReversesAccelerationField → ⊥
oppositeSearchRoleDoesNotAutomaticallyReverseAcceleration ()

------------------------------------------------------------------------
-- Search boundary used by the AG proof-search programme.
------------------------------------------------------------------------

record AntigravityNonGeometricOppositeBoundary : Set where
  constructor antigravity-non-geometric-opposite-boundary
  field
    couplingSignFlipConstructsGeometricOppositeMetric : Bool
    fixedMetricSignedCouplingRelabelIsPhysicalAntipode : Bool
    oppositeSearchRoleReversesAccelerationAutomatically : Bool

    geometricOppositeRequiresSolvedGeometryReceipt : Bool
    sourceMustBeResolvedUnderAlternativeCoupling : Bool
    observableMustBeReprojectedFromResolvedMetric : Bool
    sameObjectComparatorMustHoldFixedExperimentalInputs : Bool

canonicalAntigravityNonGeometricOppositeBoundary :
  AntigravityNonGeometricOppositeBoundary
canonicalAntigravityNonGeometricOppositeBoundary =
  antigravity-non-geometric-opposite-boundary
    false false false
    true true true true
