module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound52SourceRGFederbushValidation where

------------------------------------------------------------------------
-- Focused Round-52 validation root.
--
-- This round combines the two shortest currently available routes:
--
-- G1 / source chart:
--   principal-log scalar endpoint modulus + selected coordinates
--     -> a concrete J_j-I bound;
--   physical T_j = Ad_{U_j V^-1}
--     -> a concrete T_j-I bound;
--   exact JT-I telescope + normalized averaging
--     -> determinant-free inverse reopening.
--
-- The tiny rho/96 identity-chart specialization imported below is a checked
-- local calibration lane, not a claim that CMP109's whole 1/24 source chart is
-- that small.  The source-scale quarter estimate must consume the actual
-- source Y-radius constants without silently replacing them by rho/96.
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
--   inverse-threshold propagation.  This is weaker than, and logically prior
--   to, the still-missing full positive two-sided beta enclosure.
--
-- No Clay promotion is made here.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound51CentreKKTBetaValidation
import DASHI.Physics.YangMills.BalabanCMP109FederbushLogTransportToNormalizedInverseExact as Fed
import DASHI.Physics.YangMills.BalabanCMP109FederbushTransportResidualControlsNormExact as TransportNorm
import DASHI.Physics.YangMills.BalabanCMP109FederbushPrimitiveDefectsToNormalizedInverseExact as Primitive
import DASHI.Physics.YangMills.BalabanCMP109FederbushTransportDefectFromIdentityChartExact as TransportChart
import DASHI.Physics.YangMills.BalabanCMP109PrincipalLogDefectFromEndpointModulusExact as LogEndpoint
import DASHI.Physics.YangMills.BalabanCMP109FederbushPhysicalChartToNormalizedInverseExact as PhysicalChart
import DASHI.Physics.YangMills.BalabanCMP109FederbushCoefficientChartToInverseExact as CoefficientChart
import DASHI.Physics.YangMills.BalabanYM4NonnegativeBetaFinitePropagationExact as BetaFinite
import DASHI.Physics.YangMills.BalabanYM4BetaSplitToSmallCouplingMonotonicityExact as BetaSplit
import DASHI.Physics.YangMills.BalabanClayGate4LightweightValidation as Gate4
import DASHI.Physics.YangMills.Balaban1989CompleteDensityToYM4RegionExact as Complete
import DASHI.Physics.YangMills.Balaban1989CanonicalYM4StateFromSection2Exact as Canonical

federbushLogTransportToLocalResidualLevel =
  Fed.cmp109FederbushLogTransportToLocalResidualLevel

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

federbushPhysicalChartToInverseLevel =
  PhysicalChart.cmp109FederbushPhysicalChartToInverseLevel

federbushCoefficientChartToInverseLevel =
  CoefficientChart.cmp109FederbushCoefficientChartToInverseLevel

federbushCoefficientAndChordInputsLevel =
  CoefficientChart.physicalCMP109FederbushCoefficientAndChordInputsLevel

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
