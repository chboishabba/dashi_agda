{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261005RExact where

------------------------------------------------------------------------
-- OVERLAY R / 2026-10-05: RESEARCH FRONTIER BELOW Q1/Q2/Q3.
--
-- Q3's pointwise same-finite-sequence field was still presentation debt.
-- The Local-C transport already uses CMP119 approximateExpectation, while the
-- physical-Haar side was compiled through sourceExpectation.  The new P3
-- compiler puts the Haar representation on the SAME approximateExpectation
-- sequence and pays the difference with
--
--   quadratureError + factorizedDensityExpectationError,
--
-- both already known to vanish.  Thus no pointwise finite-sequence weld is a
-- source theorem anymore.
--
-- Q2 is sharpened by the primary trace-anomaly literature: the genuine source
-- theorem is the Weyl/Callan--Symanzik Ward identity for the renormalized
-- Hilbert energy-momentum tensor and renormalized F^2 operator.  R136 already
-- computes the Hilbert trace of the same pinned Local-C stress, and the SU(2)
-- normalization coefficient is repository algebra.  No arbitrary trace scalar
-- or normalization weld remains.
--
-- Q1 is likewise sharpened.  Invariant-potential differentiation has already
-- compiled signed B4 covariance.  BC2 owns an abstract firstVariation, but the
-- current source carrier does not expose the literal compact-gauge one-parameter
-- path x exp(tX).  The remaining theorem is therefore the source-geometric path
-- realization and its identification with BC2 firstVariation, not covariance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyP1InvariantPathDerivativeCovarianceExact as P1
import DASHI.Physics.Foundations.CMP119CosmologyP1PresentCutPathDerivativeExact as P1Cut
import DASHI.Physics.Foundations.CMP119CosmologyP2HilbertTraceAnomalyExact as P2
import DASHI.Physics.Foundations.CMP119CosmologyP3LocalCF2PhysicalHaarCommonLimitExact as P3
import DASHI.Physics.Foundations.CMP119CosmologyP3ApproximateExpectationHaarExact as P3Compile

remainingPreferredSourcePackageCount : Nat
remainingPreferredSourcePackageCount = 3

------------------------------------------------------------------------
-- R1 / Q1: literal compact-gauge source-path realization.
------------------------------------------------------------------------

primitiveSignedCovarianceStillRequired : Bool
primitiveSignedCovarianceStillRequired = false

signedCovarianceCompilerOwned : Bool
signedCovarianceCompilerOwned =
  P1.p1SignedCovarianceIsCompilerOutputFromInvariantPathDerivative

q1LocalD1CovarianceStillPremise : Bool
q1LocalD1CovarianceStillPremise = false

q1RemainingTheoremIsLiteralCompactGaugeSourcePathRealization : Bool
q1RemainingTheoremIsLiteralCompactGaugeSourcePathRealization = true

q1NeedsSourcePathEquivarianceAndBC2DerivativeIdentification : Bool
q1NeedsSourcePathEquivarianceAndBC2DerivativeIdentification = true

------------------------------------------------------------------------
-- R2 / Q2: renormalized Hilbert/Weyl trace anomaly.
------------------------------------------------------------------------

freeTraceFrameCalibrationStillRequired : Bool
freeTraceFrameCalibrationStillRequired = false

r136IsSamePinnedLocalCHilbertTraceCompilerOwned : Bool
r136IsSamePinnedLocalCHilbertTraceCompilerOwned = true

q2RemainingTheoremIsRenormalizedHilbertWeylWardIdentity : Bool
q2RemainingTheoremIsRenormalizedHilbertWeylWardIdentity = true

q2SU2CoefficientAlgebraStillOpen : Bool
q2SU2CoefficientAlgebraStillOpen = false

------------------------------------------------------------------------
-- R3 / Q3: source observable + Haar geometry, no sequence weld.
------------------------------------------------------------------------

q3PointwiseFiniteSequenceWeldRetired : Bool
q3PointwiseFiniteSequenceWeldRetired = true

q3ApproximateExpectationHaarCompilerOwned : Bool
q3ApproximateExpectationHaarCompilerOwned =
  P3Compile.compiledHaarUsesSameApproximateF2Sequence

q3CombinedVanishingErrorCompilerOwned : Bool
q3CombinedVanishingErrorCompilerOwned =
  P3Compile.physicalHaarApproximateExpectationUsesCombinedVanishingError

q3CommonLimitAnalysisCompilerOwned : Bool
q3CommonLimitAnalysisCompilerOwned =
  P3.p3CommonLimitIsOrdinaryAnalysisNotNewAnomalyPhysics

q3RemainingSourceWorkIsSelectedF2ObservableAndLiteralHaarQuadrature : Bool
q3RemainingSourceWorkIsSelectedF2ObservableAndLiteralHaarQuadrature = true

------------------------------------------------------------------------
-- Dominated lanes stay retired.
------------------------------------------------------------------------

preferredRouteNeedsEq223VacuumGap : Bool
preferredRouteNeedsEq223VacuumGap = false

preferredRouteNeedsFiniteDGammaR109Tail : Bool
preferredRouteNeedsFiniteDGammaR109Tail = false

remainingAdapterDebtInScopedPreferredRoute : Nat
remainingAdapterDebtInScopedPreferredRoute = 0

remainingWorkIsSourceGeometryWardIdentityAndMeasureConstruction : Bool
remainingWorkIsSourceGeometryWardIdentityAndMeasureConstruction = true

newMathHasRetiredP1P2P3PresentationWelds : Bool
newMathHasRetiredP1P2P3PresentationWelds = true
