module DASHI.Cognition.AnalyticLogPolarSpiralCompilerExact where

open import Agda.Builtin.Equality using (_≡_; refl; sym; cong; trans)
open import Agda.Builtin.String using (String)

open import DASHI.Analysis.ConstructiveRealSpine

import DASHI.Cognition.CorticalLogPolarProjectionGeometry as Geometry
import DASHI.Cognition.KlueverFormConstantProjection as Kluver

------------------------------------------------------------------------
-- ANALYTIC LOG-POLAR SPIRAL COMPILER
--
-- For an affine log-polar phase
--
--   phi(r,theta) = a log(r) + b theta,
--
-- a constant-phase equation can be rearranged (when a != 0) to
--
--   log(r) = q(theta)
--
-- and therefore
--
--   r = exp(q(theta)).
--
-- The second implication is closed here using the repo's constructed
-- exponential/logarithm inverse law.  The first algebraic rearrangement needs
-- a division/subtraction authority stronger than the minimal current
-- ConstructedOrderedCompleteReal signature and remains an explicit input.
------------------------------------------------------------------------

module _ (P : ConstructedRealTranscendentalPackage) where

  private
    R = real P
    E = exponential P
    L = logarithm P

  logRadiusEqualityImpliesExponentialRadius :
    (radius q : Real R) →
    (radiusPositive : Positive E radius) →
    log L radius radiusPositive ≡ q →
    radius ≡ exp E q
  logRadiusEqualityImpliesExponentialRadius
    radius q radiusPositive logRadiusIsQ =
    trans
      (sym (expLog L radius radiusPositive))
      (cong (exp E) logRadiusIsQ)

  exponentialRadiusImpliesLogRadiusEquality :
    (q : Real R) →
    log L (exp E q) (expPositive E q) ≡ q
  exponentialRadiusImpliesLogRadiusEquality q =
    logExp L q

  record AffineLogPolarPhase : Set where
    constructor affineLogPolarPhase
    field
      radialCoefficient : Real R
      angularCoefficient : Real R
      phaseConstant : Real R

      solvedLogRadius :
        Real R → Real R

      -- This is the current algebraic min-cut:
      -- from a*log(r)+b*theta=c, derive log(r)=solvedLogRadius(theta).
      ConstantPhaseEquation : Real R → Real R → Set

      constantPhaseSolvesLog :
        (radius theta : Real R) →
        (radiusPositive : Positive E radius) →
        ConstantPhaseEquation radius theta →
        log L radius radiusPositive ≡ solvedLogRadius theta

  open AffineLogPolarPhase public

  record AnalyticSpiralPoint
      (phase : AffineLogPolarPhase) : Set where
    constructor analyticSpiralPoint
    field
      radius : Real R
      theta : Real R
      radiusPositive : Positive E radius
      constantPhase :
        AffineLogPolarPhase.ConstantPhaseEquation phase radius theta

  open AnalyticSpiralPoint public

  analyticSpiralPointHasExponentialRadius :
    (phase : AffineLogPolarPhase) →
    (point : AnalyticSpiralPoint phase) →
    AnalyticSpiralPoint.radius point
    ≡
    exp E
      (AffineLogPolarPhase.solvedLogRadius phase
        (AnalyticSpiralPoint.theta point))
  analyticSpiralPointHasExponentialRadius phase point =
    logRadiusEqualityImpliesExponentialRadius
      (AnalyticSpiralPoint.radius point)
      (AffineLogPolarPhase.solvedLogRadius phase
        (AnalyticSpiralPoint.theta point))
      (AnalyticSpiralPoint.radiusPositive point)
      (AffineLogPolarPhase.constantPhaseSolvesLog phase
        (AnalyticSpiralPoint.radius point)
        (AnalyticSpiralPoint.theta point)
        (AnalyticSpiralPoint.radiusPositive point)
        (AnalyticSpiralPoint.constantPhase point))

------------------------------------------------------------------------
-- Connection to the existing coarse visual-mode vocabulary.
------------------------------------------------------------------------

data AnalyticSpiralProjectionStatus : Set where
  exponentialRadiusLawClosed : AnalyticSpiralProjectionStatus
  affineRearrangementRequiresDivisionAuthority : AnalyticSpiralProjectionStatus
  empiricalModeIdentificationOpen : AnalyticSpiralProjectionStatus

analyticFeature : Geometry.VisualModeFeature
analyticFeature = Geometry.angularPhaseDrift

analyticForm : Kluver.KlueverForm
analyticForm = Kluver.spiral

analyticFeatureProjectsAsSpiral :
  Geometry.FeatureProjectsAs analyticFeature analyticForm
analyticFeatureProjectsAsSpiral =
  Geometry.angularDriftAsSpiral

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record AnalyticLogPolarSpiralBoundary : Set where
  constructor analyticLogPolarSpiralBoundary
  field
    expLogRadiusCompilerProved : Bool
    expLogRadiusCompilerProvedIsTrue :
      expLogRadiusCompilerProved ≡ true

    affineConstantPhaseRearrangementProvedFromCurrentMinimalRealSpine : Bool
    affineConstantPhaseRearrangementProvedFromCurrentMinimalRealSpineIsFalse :
      affineConstantPhaseRearrangementProvedFromCurrentMinimalRealSpine
      ≡ false

    empiricalV1SpatialModeIdentifiedAsAffineLogPolarPhase : Bool
    empiricalV1SpatialModeIdentifiedAsAffineLogPolarPhaseIsFalse :
      empiricalV1SpatialModeIdentifiedAsAffineLogPolarPhase ≡ false

    logarithmicSpiralPhenomenologyRecovered : Bool
    logarithmicSpiralPhenomenologyRecoveredIsFalse :
      logarithmicSpiralPhenomenologyRecovered ≡ false

canonicalAnalyticLogPolarSpiralBoundary :
  AnalyticLogPolarSpiralBoundary
canonicalAnalyticLogPolarSpiralBoundary =
  analyticLogPolarSpiralBoundary
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Exact remaining theorem target.
------------------------------------------------------------------------

record AffinePhaseRearrangementFrontier : Set where
  constructor affinePhaseRearrangementFrontier
  field
    existingAnalyticOwner : String
    missingAlgebraicAuthority : String
    targetEquation : String
    compiledConsequence : String
    empiricalGuard : String

canonicalAffinePhaseRearrangementFrontier :
  AffinePhaseRearrangementFrontier
canonicalAffinePhaseRearrangementFrontier =
  affinePhaseRearrangementFrontier
    "DASHI.Analysis.ConstructiveRealSpine supplies constructed exp/log and expLog/logExp inverse laws"
    "field/division plus subtraction-as-additive-inverse laws sufficient to rearrange a*log(r)+b*theta=c for nonzero a"
    "log(r) = a^{-1} * (c - b*theta)"
    "r = exp(a^{-1} * (c - b*theta)), i.e. an exponential/logarithmic spiral radius law"
    "the analytic compiler does not assert that any measured V1 field or reported hallucination inhabits the affine phase model"
