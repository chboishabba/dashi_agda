{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound102PhysicalCutExact where

------------------------------------------------------------------------
-- ROUND102: CURRENT SHORTEST PHYSICAL BIDI CUT
--
-- A, backward from the frozen completion:
--   SAME CMP109 mixed beta scalar
--   + history-uniform two-sided Gaussian/five-channel enclosure
--   + source shooting self-map / q<1 fixed point
--     -> pointwise beta slopes
--     -> prefix + terminal tails
--     -> exact terminal renormalised coordinate
--     -> frozen Row-A completion after literal source instantiation.
--
-- B/C, forward from CMP109/CMP116:
--   ONE differentiated effective-density carrier
--   + SAME hessian-mark analytic shell reused by first gradients
--   + standard bounded-gradient covariance inequality
--     -> temporal Heat/Doob curvature debt
--     -> dynamic weighted influence row
--     -> every weighted power
--     -> positive Dyson quasi-local series.
--
-- The false generic eta=H / dynamic=static shortcut remains superseded.  The
-- covariance is genuine; its localization reduces to first-gradient Cauchy data.
--
-- AUTHORITY: no physical source-instantiation record is fabricated here.
-- Frozen A/B/C/D count remains four until the literal completion predicates are
-- inhabited.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound101BidiCompletionCutExact as R101
import DASHI.Physics.YangMills.BalabanYM4FiveChannelQuarticAbsoluteBetaRound102Exact as ATwoChannel
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as ATwo
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

rowAShootingFixedPointTerminalCoordinateRound102Level : ProofLevel
rowAShootingFixedPointTerminalCoordinateRound102Level =
  AShoot.shootingFixedPointTerminalCoordinateLevel

rowAShootingFixedPointTerminalCouplingRound102Level : ProofLevel
rowAShootingFixedPointTerminalCouplingRound102Level =
  AShoot.shootingFixedPointTerminalCouplingLevel

-- Actual source-facing A seam after all compiler collapse.
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

-- Actual source-facing B/C seam after all compiler collapse.
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
