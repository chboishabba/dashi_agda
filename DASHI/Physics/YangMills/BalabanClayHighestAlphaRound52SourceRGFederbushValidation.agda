module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound52SourceRGFederbushValidation where

------------------------------------------------------------------------
-- Focused Round-52 validation root.
--
-- G1 / source chart -- preferred route:
--
--   D_-(Y) Ad_{exp Y} = D_+(Y),
--   J_+ = D_+^-1, J_- = D_-^-1
--       => J_+(Y) Ad_{exp Y} = J_-(Y).
--
-- Therefore the physical component does NOT need separately majorized
-- principal-log and transport defects.  It inherits one opposite-trivialization
-- inverse-dexp defect, whose source |Y|<=1/12 envelope is already <<1/4.
-- Normalized contour averaging then gives the determinant-free 4/3 reopening.
--
-- The older JT-I triangle and the rho/96 identity-chart specialization remain
-- imported as diagnostic/calibration lanes only; they are no longer presented
-- as the shortest source-scale conditioning route.
--
-- RG1a/RG1b / complete density:
--   CMP109 rooted localization summability
--   + CMP119/CMP122 R-operation and boundary preservation
--   + CMP99 background propagator authority
--   + sufficiently-small coupling history
--     -> direct Sect.-2 complete-density -> canonical YM4 invariant-region state.
--
-- RG1e / coupling history:
--   beta split -> beta>=0 -> finite inverse-coupling monotonicity -> backwards
--   inverse-threshold propagation.  This is weaker than the still-missing full
--   positive two-sided beta enclosure, and is sufficient for the monotonic part
--   of the CMP122 small-coupling hypothesis.
--
-- No Clay promotion is made here.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound51CentreKKTBetaValidation
import DASHI.Physics.YangMills.BalabanCMP109FederbushDexpTransportCancellationExact as Cancellation
import DASHI.Physics.YangMills.BalabanCMP109FederbushCancellationNormalizedInverseExact as CancellationInverse
import DASHI.Physics.YangMills.BalabanCMP109FederbushSourceScaleQuarterExact as SourceScale
import DASHI.Physics.YangMills.BalabanCMP109FederbushSourceScaleNormalizedInverseExact as SourceScaleInverse
import DASHI.Physics.YangMills.BalabanCMP109FederbushTransportResidualControlsNormExact as TransportNorm
import DASHI.Physics.YangMills.BalabanCMP109FederbushPrimitiveDefectsToNormalizedInverseExact as Primitive
import DASHI.Physics.YangMills.BalabanCMP109FederbushTransportDefectFromIdentityChartExact as TransportChart
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogDefectFromEndpointModulusExact as LogEndpoint
import DASHI.Physics.YangMills.BalabanCMP109FederbushCoefficientChartToInverseExact as CoefficientChart
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as BetaFinite
import DASHI.Physics.YangMills.BalabanYM4BetaSplitToSmallCouplingMonotonicityExact as BetaSplit
import DASHI.Physics.YangMills.BalabanClayGate4LightweightValidation as Gate4
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToYM4RegionExact as Complete
import DASHI.Physics.YangMills.Balaban1989CanonicalYM4StateFromSection2Exact as Canonical

federbushDexpTransportCancellationLevel =
  Cancellation.cmp109FederbushDexpTransportCancellationLevel

federbushPhysicalDexpTransportIdentificationLevel =
  Cancellation.cmp109FederbushPhysicalDexpTransportIdentificationLevel

federbushCancellationResidualQuarterLevel =
  CancellationInverse.cmp109FederbushCancellationResidualQuarterLevel

federbushCancellationFourThirdsInverseLevel =
  CancellationInverse.cmp109FederbushCancellationFourThirdsInverseLevel

federbushCancellationMatrixDictionaryLevel =
  CancellationInverse.cmp109FederbushCancellationMatrixDictionaryLevel

federbushSourceScaleQuarterArithmeticLevel =
  SourceScale.cmp109FederbushSourceScaleQuarterArithmeticLevel

federbushSourceScaleFourThirdsInverseLevel =
  SourceScaleInverse.cmp109FederbushSourceScaleFourThirdsInverseLevel

-- Secondary diagnostics/calibrations.
federbushTransportDefectControlsNormLevel =
  TransportNorm.cmp109FederbushTransportDefectControlsNormLevel

federbushPrimitiveDefectsToInverseLevel =
  Primitive.cmp109FederbushPrimitiveDefectsToInverseLevel

federbushTinyIdentityChartCalibrationLevel =
  TransportChart.cmp109FederbushTransportDefectFromIdentityChartLevel

principalLogEndpointModulusToDefectLevel =
  LogEndpoint.cmp109PrincipalLogEndpointModulusToDefectLevel

principalLogBishopCoefficientToRationalLevel =
  LogEndpoint.cmp109PrincipalLogBishopCoefficientToRationalLevel

federbushCoefficientChartToInverseLevel =
  CoefficientChart.cmp109FederbushCoefficientChartToInverseLevel

nonnegativeBetaFiniteMonotonicityLevel =
  BetaFinite.ym4NonnegativeBetaFiniteMonotonicityLevel

inverseThresholdBackwardPropagationLevel =
  BetaFinite.ym4InverseThresholdBackwardPropagationLevel

betaSplitNonnegativeTrajectoryLevel =
  BetaSplit.ym4BetaSplitNonnegativeTrajectoryLevel

betaSplitFiniteSmallCouplingMonotonicityLevel =
  BetaSplit.ym4BetaSplitFiniteSmallCouplingMonotonicityLevel

completeDensityToYM4RegionAssemblyLevel =
  Complete.balabanCompleteDensityToYM4RegionAssemblyLevel

canonicalYM4StateConstructionLevel =
  Canonical.balaban1989CanonicalYM4StateConstructionLevel

canonicalSection2ToYM4RegionLevel =
  Canonical.balaban1989CanonicalSection2ToYM4RegionLevel

section2ScalarCoordinateExtractionLevel =
  Canonical.balaban1989Section2ScalarCoordinateExtractionLevel

cmp109RootedLocalizationSummabilityLevel =
  Gate4.cmp109Equation026RootedSummabilityLevel

cmp109CMP122DirectRootedRAssemblyLevel =
  Gate4.cmp109CMP122DirectRootedRAssemblyLevel

balabanPhysicalSmallCouplingHistoryLevel =
  Gate4.balabanPhysicalSmallCouplingHistoryLevel
