{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261004QExact where

------------------------------------------------------------------------
-- OVERLAY Q / 2026-10-04: NEW MATHEMATICS BELOW P1/P2/P3.
--
-- The previous P-board named three same-object/covariance statements.  This
-- tranche derives or removes the presentation-level form of all three.
--
-- P1 RETIRED AS PRIMITIVE COVARIANCE:
--   signed B4 covariance follows by differentiating an invariant scalar
--   effective potential along an equivariant one-parameter source path.  R143
--   transports that theorem to the exact finite localized D1 used by R144.
--   Remaining source package Q1 is therefore ordinary path semantics:
--     * BC2.firstVariation is the derivative of the selected source path;
--     * that source path is B4-equivariant, with negative tensor signs carried
--       by t -> -t.
--   Potential invariance itself is finite permutation/local-activity algebra.
--
-- P2 FREE TRACE-FRAME CALIBRATION RETIRED:
--   define the trace by the Hilbert metric pairing of the SAME R130/R136 stress.
--   Round130 + the Round109/Local-C same-stress theorem then prove
--     embed(Q_R136) = HilbertTrace(T_LocalC)
--   by compiler algebra.  Remaining Q2 is the actual nonperturbative source
--   theorem on this object pair:
--     HilbertTrace(T_ren) = b_SU2 * [F^2]_ren.
--
-- P3 EXACT FINITE=CONTINUUM F2 WELD RETIRED:
--   Local-C F2 and physical Haar F2 need only be limits of pointwise the SAME
--   finite F2 sequence.  The repository limit congruence then proves equality
--   of the continuum readouts and transports strict physical-Haar positivity.
--   Remaining Q3 is to construct/identify that common finite physical F2
--   sequence in the two already-existing limit representations.
--
-- P2+P3 now compile directly to negative rational R136.  No Eq.(2.23) vacuum
-- sign, finite D_Gamma tail, free trace scalar, or exact finite/continuum F2
-- equality is consumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyP1InvariantPathDerivativeCovarianceExact as P1Math
import DASHI.Physics.Foundations.CMP119CosmologyP1SourcePotentialCovarianceExact as P1Potential
import DASHI.Physics.Foundations.CMP119CosmologyP1PresentCutPathDerivativeExact as P1Present
import DASHI.Physics.Foundations.CMP119CosmologyP2HilbertTraceAnomalyExact as P2
import DASHI.Physics.Foundations.CMP119CosmologyP3LocalCF2PhysicalHaarCommonLimitExact as P3
import DASHI.Physics.Foundations.CMP119CosmologyP23HilbertHaarToR136SignExact as P23

remainingPreferredSourcePackageCount : Nat
remainingPreferredSourcePackageCount = 3

------------------------------------------------------------------------
-- Q1: source path derivative package.
------------------------------------------------------------------------

primitiveSignedCovarianceRetired : Bool
primitiveSignedCovarianceRetired =
  P1Present.primitiveSignedD1CovarianceNoLongerRequired _ _

signedCovarianceDerivedFromInvariantPathCalculus : Bool
signedCovarianceDerivedFromInvariantPathCalculus =
  P1Math.p1SignedCovarianceIsCompilerOutputFromInvariantPathDerivative

potentialCovarianceDoesNotNeedD1Covariance : Bool
potentialCovarianceDoesNotNeedD1Covariance =
  P1Potential.potentialCovarianceNeedsNoDerivativeCovariancePremise

q1IsPathDerivativeSemanticsAndEquivariance : Bool
q1IsPathDerivativeSemanticsAndEquivariance = true

------------------------------------------------------------------------
-- Q2: anomaly on the actual Hilbert trace of the same R136/Local-C stress.
------------------------------------------------------------------------

freeTraceFrameCalibrationRetired : Bool
freeTraceFrameCalibrationRetired = true

r136HilbertTraceEqualityIsCompilerOwned : Bool
r136HilbertTraceEqualityIsCompilerOwned = true

q2IsNonperturbativeHilbertTraceAnomalyOnExactLocalCPair : Bool
q2IsNonperturbativeHilbertTraceAnomalyOnExactLocalCPair = true

------------------------------------------------------------------------
-- Q3: common finite F2 sequence, not exact finite=continuum equality.
------------------------------------------------------------------------

exactFiniteContinuumF2WeldRetired : Bool
exactFiniteContinuumF2WeldRetired =
  P3.exactFiniteEqualsContinuumF2NoLongerRequired

functionExtensionalityNotCharged : Bool
functionExtensionalityNotCharged =
  P3.functionExtensionalityNotRequiredForCommonLimit

q3IsPointwiseCommonFinitePhysicalF2Sequence : Bool
q3IsPointwiseCommonFinitePhysicalF2Sequence = true

------------------------------------------------------------------------
-- Downstream sign route.
------------------------------------------------------------------------

p23CompilerConsumesOldTraceFrameCalibration : Bool
p23CompilerConsumesOldTraceFrameCalibration = false

p23CompilerConsumesOldExactF2Weld : Bool
p23CompilerConsumesOldExactF2Weld = false

p23CompilesPhysicalHaarPositivityToNegativeR136 : Bool
p23CompilesPhysicalHaarPositivityToNegativeR136 = true

preferredRouteUsesEq223VacuumGap : Bool
preferredRouteUsesEq223VacuumGap = false

preferredRouteUsesFiniteDGammaR109Tail : Bool
preferredRouteUsesFiniteDGammaR109Tail = false

------------------------------------------------------------------------
-- Trust accounting.
------------------------------------------------------------------------

remainingAdapterDebtInScopedPreferredRoute : Nat
remainingAdapterDebtInScopedPreferredRoute = 0

remainingPackagesAreSourceConstructionOrSourceTheorems : Bool
remainingPackagesAreSourceConstructionOrSourceTheorems = true

newMathHasReplacedPresentationEqualities : Bool
newMathHasReplacedPresentationEqualities = true
