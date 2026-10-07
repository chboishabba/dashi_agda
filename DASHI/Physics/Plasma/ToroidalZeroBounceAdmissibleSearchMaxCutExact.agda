module DASHI.Physics.Plasma.ToroidalZeroBounceAdmissibleSearchMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.ToroidalZeroBounceAdmissibleConeSearchExact as Cone
import DASHI.Physics.Plasma.ToroidalZeroBounceContinuationExact as Continuation
import DASHI.Physics.Plasma.ToroidalZeroBounceGeometryParetoExact as GeometryPareto
import DASHI.Physics.Plasma.ToroidalZeroBounceCurvatureMaxCutExact as CurvatureCut
import DASHI.Physics.Plasma.ZeroBouncePopulationExact as ZeroBounce

------------------------------------------------------------------------
-- SEARCH-SPACE COMPRESSION MAX-CUT
--
-- Hard physics -> tangent/nullspace cone -> active inequality cone -> C_(3^n)
-- spectral quotient -> delta_C continuation -> N-dimensional Pareto frontier.
------------------------------------------------------------------------

record AdmissibleSearchMaxCut
    (population : ZeroBounce.DeclaredParticlePopulation) : Set₁ where
  constructor admissible-search-max-cut
  field
    coneSearch : Cone.ToroidalAdmissibleConeSearch population
    continuation : Continuation.AdmissibleContinuationPath coneSearch
    hardPhysicsBeforeObjectiveReceipt : Set
    equalityNullspaceBeforeNumericalDescentReceipt : Set
    activeInequalityConeReceipt : Set
    triadicSpectralQuotientReceipt : Set
    zeroBouncePreservedAcrossSearchReceipt : Set
    bestKnownReferenceConsumerPreservedReceipt : Set
    finiteOrbitWidthConsumerPreservedReceipt : Set
    energeticParticleConsumerPreservedReceipt : Set
    coilInverseProblemDownstreamReceipt : Set
    maxCutReference : String

open AdmissibleSearchMaxCut public

record AdmissibleSearchBoundary : Set where
  constructor admissible-search-boundary
  field
    severeExactConstraintsAreOnlyAnObstacle : Bool
    severeExactConstraintsAreOnlyAnObstacleIsFalse :
      severeExactConstraintsAreOnlyAnObstacle ≡ false

    constraintsMayCompressSearchSpaceConstructively : Bool
    constraintsMayCompressSearchSpaceConstructivelyIsTrue :
      constraintsMayCompressSearchSpaceConstructively ≡ true

    zeroTangentConeMeansOptimizerFailureOnly : Bool
    zeroTangentConeMeansOptimizerFailureOnlyIsFalse :
      zeroTangentConeMeansOptimizerFailureOnly ≡ false

    disconnectedAdmissibleConesMayFormHyperfabricPatches : Bool
    disconnectedAdmissibleConesMayFormHyperfabricPatchesIsTrue :
      disconnectedAdmissibleConesMayFormHyperfabricPatches ≡ true

    commercialScoringPrecedesPhysicsAdmissibility : Bool
    commercialScoringPrecedesPhysicsAdmissibilityIsFalse :
      commercialScoringPrecedesPhysicsAdmissibility ≡ false

canonicalAdmissibleSearchBoundary : AdmissibleSearchBoundary
canonicalAdmissibleSearchBoundary =
  admissible-search-boundary
    false refl
    true refl
    false refl
    true refl
    false refl

searchOrderReference : String
searchOrderReference =
  "hard constraints -> nullspace/tangent cone -> inequalities -> C_(3^n) quotient -> delta_C continuation -> Pareto -> coils/orbits"
