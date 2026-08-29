{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound102PhysicalCutExact where

------------------------------------------------------------------------
-- ROUND102: CURRENT SHORTEST PHYSICAL BIDI CUT
--
-- A, backward from the frozen completion:
--   SAME CMP109 mixed beta scalar
--   + history-uniform two-sided Gaussian/five-channel enclosure
--   + canonical Q->R ordered transport
--   + q<1 source shooting sensitivity
--     -> pointwise real beta slopes
--     -> cumulative beta interval
--     -> shooting tube self-map automatically
--     -> Banach fixed point
--     -> exact terminal renormalised inverse-square coordinate/coupling
--     -> prefix + terminal tails / frozen Row-A compiler.
--
-- B/C, forward from CMP109/CMP116:
--   ONE differentiated effective-density carrier
--   + SAME hessian-mark analytic shell reused by first gradients
--   + standard bounded-gradient covariance inequality
--     -> temporal Heat/Doob curvature debt
--     -> dynamic weighted influence row
--     -> every weighted power
--     -> entrywise weighted quasi-locality
--     -> positive Dyson quasi-local series.
--
-- The false generic eta=H / dynamic=static shortcut remains superseded.  The
-- covariance is genuine; its localization reduces to first-gradient Cauchy data.
-- Frozen A/B/C/D count remains four until literal source completion predicates
-- are inhabited.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound101BidiCompletionCutExact as R101
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticAbsoluteBetaRound102Exact as ATwoChannel
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as ATwo
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as AReal
import DASHI.Physics.YangMills.BalabanRowAShootingTubeFromBetaBoundsRound102Exact as ATube
import DASHI.Physics.YangMills.BalabanRowAShootingFixedPointTerminalExactRound102 as AShoot
import DASHI.Physics.YangMills.BalabanCMP109116SameDifferentiatedCarrierRound102Exact as Same
import DASHI.Physics.YangMills.BalabanCMP116FirstGradientSharedMarkedExact as GradMarked
import DASHI.Physics.YangMills.BalabanHeatDoobGradientCovarianceMarkedCauchyExact as GradCov
import DASHI.Physics.YangMills.BalabanCMP116GradientCovarianceToHeatDoobDebtExact as Temporal
import DASHI.Physics.YangMills.BalabanCMP116GradientCovarianceToWeightedHeatDoobExact as Spatial
import DASHI.Physics.YangMills.BalabanWeightedInfluenceEntryQuasiLocalExact as Entry
import DASHI.Physics.YangMills.BalabanWeightedDysonQuasiLocalSeriesExact as Dyson

------------------------------------------------------------------------
-- A
------------------------------------------------------------------------

rowAFiveChannelTwoSidedQuarticRound102Level : ProofLevel
rowAFiveChannelTwoSidedQuarticRound102Level =
  ATwoChannel.fiveChannelQuarticAbsoluteBetaLevel

rowAHistoryUniformTwoSidedPointwiseBetaRound102Level : ProofLevel
rowAHistoryUniformTwoSidedPointwiseBetaRound102Level =
  ATwo.historyUniformTwoSidedBetaRound102Level

rowARationalCertificateToRealSlopesRound102Level : ProofLevel
rowARationalCertificateToRealSlopesRound102Level =
  AReal.rationalCertificateToRealBetaSlopeLevel

rowATwoSidedBetaMakesShootingTubeInvariantRound102Level : ProofLevel
rowATwoSidedBetaMakesShootingTubeInvariantRound102Level =
  ATube.shootingTubeFromBetaBoundsLevel

rowAShootingFixedPointTerminalCoordinateRound102Level : ProofLevel
rowAShootingFixedPointTerminalCoordinateRound102Level =
  AShoot.shootingFixedPointTerminalCoordinateLevel

rowAShootingFixedPointTerminalCouplingRound102Level : ProofLevel
rowAShootingFixedPointTerminalCouplingRound102Level =
  AShoot.shootingFixedPointTerminalCouplingLevel

-- Remaining literal A source instantiation is now concentrated in:
--   * SAME-object Ward/Gaussian + absolute five-channel certificate for (5.42);
--   * SAME-history q<1 shooting sensitivity.
-- Two-sided beta bounds themselves give the closed shooting tube; Banach is
-- standard analysis; the fixed point gives the exact terminal target.
rowAPhysicalSourceInstantiationRound102Level : ProofLevel
rowAPhysicalSourceInstantiationRound102Level = conditional

------------------------------------------------------------------------
-- B/C
------------------------------------------------------------------------

rowBCSameDifferentiatedCarrierIdentityRound102Level : ProofLevel
rowBCSameDifferentiatedCarrierIdentityRound102Level =
  Same.sameDifferentiatedCarrierIdentityLevel

rowBCFirstGradientReusesCMP116MarkedShellRound102Level : ProofLevel
rowBCFirstGradientReusesCMP116MarkedShellRound102Level =
  GradMarked.cmp116FirstGradientReusesSharedMarkedShellLevel

rowBCFirstGradientWeightedRowRound102Level : ProofLevel
rowBCFirstGradientWeightedRowRound102Level =
  GradMarked.cmp116FirstGradientWeightedRowLevel

rowBCTemporalGradientCovarianceShellRound102Level : ProofLevel
rowBCTemporalGradientCovarianceShellRound102Level =
  GradCov.temporalGradientCovarianceShellCompilerLevel

rowBCSpatialGradientCovarianceRowRound102Level : ProofLevel
rowBCSpatialGradientCovarianceRowRound102Level =
  GradCov.spatialGradientCovarianceWeightedRowCompilerLevel

rowBCGradientCovarianceToHeatDoobDebtRound102Level : ProofLevel
rowBCGradientCovarianceToHeatDoobDebtRound102Level =
  Temporal.cmp116GradientCovarianceToHeatDoobDebtLevel

rowBCGradientCovarianceToWeightedHeatDoobRound102Level : ProofLevel
rowBCGradientCovarianceToWeightedHeatDoobRound102Level =
  Spatial.cmp116GradientCovarianceToWeightedHeatDoobLevel

rowCEntrywiseQuasiLocalPowerRound102Level : ProofLevel
rowCEntrywiseQuasiLocalPowerRound102Level =
  Entry.weightedEntryQuasiLocalPowerLevel

rowCPositiveWeightedDysonSeriesRound102Level : ProofLevel
rowCPositiveWeightedDysonSeriesRound102Level =
  Dyson.weightedPositiveDysonSeriesCompilerLevel

-- Remaining literal B/C source instantiation is ONE CMP109/116 differentiated
-- density/coordinate plus first-gradient Cauchy identification on its common
-- analytic radius.  Covariance shell/row propagation is downstream.
rowBCPhysicalSourceInstantiationRound102Level : ProofLevel
rowBCPhysicalSourceInstantiationRound102Level = conditional

------------------------------------------------------------------------
-- Frozen authority
------------------------------------------------------------------------

round102FrozenResearchCountStillFour = R101.round101FrozenResearchCountStillFour

rowACompletionRound102Level : ProofLevel
rowACompletionRound102Level = conditional

rowBCompletionRound102Level : ProofLevel
rowBCompletionRound102Level = conditional

rowCCompletionRound102Level : ProofLevel
rowCCompletionRound102Level = conditional

rowDCompletionRound102Level : ProofLevel
rowDCompletionRound102Level = conditional
