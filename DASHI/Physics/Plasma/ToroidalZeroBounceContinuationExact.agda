module DASHI.Physics.Plasma.ToroidalZeroBounceContinuationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalZeroBounceAdmissibleConeSearchExact as Cone
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- CONTINUATION / HOMOTOPY IN THE ROUTE-C GEOMETRY BURDEN
--
-- Start from an exact A+B balance with delta_C = 0, then move through only
-- admissible states while increasing the declared fraction of magnetic tension
-- paid by route-C geometry.  Continuation is a search strategy; it does not
-- assert that the pure-C endpoint is reachable.
------------------------------------------------------------------------

record GeometryResidualLevel : Set where
  constructor geometry-residual-level
  field
    Level : Set
    levelReference : String

open GeometryResidualLevel public

record AdmissibleContinuationStep
    {population : ZeroBounce.DeclaredParticlePopulation}
    (search : Cone.ToroidalAdmissibleConeSearch population) : Set₁ where
  constructor admissible-continuation-step
  field
    fromState toState : Cone.State search
    fromResidualLevel toResidualLevel : GeometryResidualLevel
    nondecreasingGeometryBurdenReceipt : Set
    enabledAdmissibleTransitionReceipt : Set
    hardInvariantsPreservedReceipt : Set
    zeroBouncePreservedReceipt : Set
    c3nSpectralChartPreservedReceipt : Set
    sameConsumerObservablesReceipt : Set
    stepReference : String

open AdmissibleContinuationStep public

record AdmissibleContinuationPath
    {population : ZeroBounce.DeclaredParticlePopulation}
    (search : Cone.ToroidalAdmissibleConeSearch population) : Set₁ where
  constructor admissible-continuation-path
  field
    StepIndex : Set
    stepAt : StepIndex → AdmissibleContinuationStep search
    startsAtExactABBoundaryReceipt : Set
    everyStepStaysInAdmissibleConeReceipt : Set
    continuationMayTerminateBeforePureCReceipt : Set
    pathReference : String

open AdmissibleContinuationPath public

record ContinuationBoundary : Set where
  constructor continuation-boundary
  field
    continuationGuaranteesPureCReachability : Bool
    continuationGuaranteesPureCReachabilityIsFalse :
      continuationGuaranteesPureCReachability ≡ false

    everyAcceptedStepPreservesHardInvariants : Bool
    everyAcceptedStepPreservesHardInvariantsIsTrue :
      everyAcceptedStepPreservesHardInvariants ≡ true

    zeroDimensionalConeIsInformativeNoGoSignal : Bool
    zeroDimensionalConeIsInformativeNoGoSignalIsTrue :
      zeroDimensionalConeIsInformativeNoGoSignal ≡ true

canonicalContinuationBoundary : ContinuationBoundary
canonicalContinuationBoundary =
  continuation-boundary false refl true refl true refl

pythonContinuationReference : String
pythonContinuationReference =
  "scripts/admissible_cone_routeC_search.py::continuation_states"
