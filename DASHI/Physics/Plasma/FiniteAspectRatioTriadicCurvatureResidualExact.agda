module DASHI.Physics.Plasma.FiniteAspectRatioTriadicCurvatureResidualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Plasma.TriadicPhaseFourierProjectorExact as Projector

------------------------------------------------------------------------
-- FINITE-ASPECT-RATIO TRIADIC CURVATURE RESIDUAL
--
-- In the explicit circular-torus helix probe, equal phase averaging suppresses
-- the radial projection of the guiding-centre curvature-drift proxy b x kappa.
-- The suppression is interpreted through the cyclic Fourier projector: C_N
-- removes all angular harmonics below N except the zero mode, so the first
-- geometry-error harmonic that can survive is pushed to mode N.
--
-- Numerical scaling data are evidence/probe receipts, not promoted analytic
-- inequalities for arbitrary toroidal equilibria.
------------------------------------------------------------------------

record FiniteAspectRatioCurvatureResidualReceipt : Set₁ where
  constructor finite-aspect-ratio-curvature-residual-receipt
  field
    majorRadiusReference : String
    minorRadiusReference : String
    aspectRatioReference : String

    curvatureDriftObservableReference : String
    singlePhaseRMSReference : String
    phaseAveragedRMSReference : String
    suppressionRatioReference : String

    c3ResidualReference : String
    c9ResidualReference : String
    c27ResidualReference : String

    phaseProjectorReceipt : Projector.CyclicFourierProjectorReceipt
    sameToroidalGeometryAcrossPhasesReceipt : Set
    sameGuidingCentreNormalizationReceipt : Set
    finiteDifferenceConvergenceReceipt : Set
    probeReference : String

open FiniteAspectRatioCurvatureResidualReceipt public

record FiniteAspectRatioResidualBoundary : Set where
  constructor finite-aspect-ratio-residual-boundary
  field
    numericalSuppressionIsUniversalAnalyticBound : Bool
    numericalSuppressionIsUniversalAnalyticBoundIsFalse :
      numericalSuppressionIsUniversalAnalyticBound ≡ false

    c27RoundoffMeansPhysicalResidualExactlyZero : Bool
    c27RoundoffMeansPhysicalResidualExactlyZeroIsFalse :
      c27RoundoffMeansPhysicalResidualExactlyZero ≡ false

    firstSurvivingHarmonicGuidesOptimization : Bool
    firstSurvivingHarmonicGuidesOptimizationIsTrue :
      firstSurvivingHarmonicGuidesOptimization ≡ true

    finiteAspectRatioResidualMustRemainExplicit : Bool
    finiteAspectRatioResidualMustRemainExplicitIsTrue :
      finiteAspectRatioResidualMustRemainExplicit ≡ true

canonicalFiniteAspectRatioResidualBoundary : FiniteAspectRatioResidualBoundary
canonicalFiniteAspectRatioResidualBoundary =
  finite-aspect-ratio-residual-boundary false refl false refl true refl true refl

r3NumericalSnapshot : String
r3NumericalSnapshot =
  "Circular torus R/r=3, m=1 guiding-centre curvature proxy: single-phase RMS about 2.5846e-1; C3 averaged RMS about 8.386e-3; C9 about 6.3e-8; C27 at numerical roundoff in the local probe."
