module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound68TopDownSZZValidation where

------------------------------------------------------------------------
-- ROUND68 FOCUSED ROOT: TOP-DOWN CLAY + BALABAN -> SZZ HANDOFF
--
-- No frontier leaf count is authoritative here.  The literal Round67 Clay
-- construction remains the endpoint.  Round68 verifies two sharper facts:
--
-- (1) the five current theorem ROLES cover every literal Clay requirement on
--     the same construction object, with no final endpoint-identification axiom;
--
-- (2) the physical mass-gap role has a shorter candidate producer than an
--     independent terminal spectral theorem: run the source-normalized Balaban
--     RG until the coarse inverse coupling and the unified-norm Hessian remainder
--     enter the Shen--Zhu--Zhu positive-curvature region, then use the published
--     functional-inequality / derivative-propagation theorem at that actual
--     coarse scale and pull the resulting gap through the existing same-object
--     transfer/continuum machinery.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.BalabanPublishedUVStabilityNonlinearRGCoreExact as UV
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified
import DASHI.Physics.YangMills.BalabanSZZWilsonCrossoverTerminalGapExact as Cross
import DASHI.Physics.YangMills.BalabanSZZHessianPerturbationExact as Hess
import DASHI.Physics.YangMills.BalabanSZZSourceNativeHessianHandoffExact as Handoff
import DASHI.Physics.YangMills.BalabanStrongCouplingPoincareBudgetExact as SZZ
import DASHI.Physics.YangMills.ShenZhuZhuGaugeInvariantGaugeFixingBridgeExact as GaugeFix
import DASHI.Physics.YangMills.BalabanFiniteScaleFourthCumulantMomentBudgetExact as Cumulant
import DASHI.Physics.YangMills.BalabanUnifiedContinuumEndpointMarginTransportExact as Margin
import DASHI.Physics.YangMills.BalabanTransferGapToObservableClusteringExact as GapCluster
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.CompactSimpleQuantitativeCoverage as Groups

round68TopDownFiveTheoremCoverageLevel : ProofLevel
round68TopDownFiveTheoremCoverageLevel = Five.topDownFiveTheoremCoverageCompilerLevel

round68PublishedUVCoreLevel : ProofLevel
round68PublishedUVCoreLevel = UV.publishedFourDimensionalNonlinearRGCoreLevel

round68SourceNormalizedCouplingTelescopeLevel : ProofLevel
round68SourceNormalizedCouplingTelescopeLevel = Flow.ym4SourceNormalizedCouplingTelescopeLevel

round68UnifiedProjectionClosureLevel : ProofLevel
round68UnifiedProjectionClosureLevel = Unified.unifiedNormProjectionClosureLevel

round68SZZNormalizationBridgeLevel : ProofLevel
round68SZZNormalizationBridgeLevel = Cross.balabanSZZNormalizationBridgeLevel

round68SZZFiniteCrossoverLevel : ProofLevel
round68SZZFiniteCrossoverLevel = Cross.balabanSZZFiniteCrossoverCompilerLevel

round68HessianPerturbationLevel : ProofLevel
round68HessianPerturbationLevel = Hess.hessianPerturbationBakryEmeryLevel

round68SourceNativeSZZHandoffLevel : ProofLevel
round68SourceNativeSZZHandoffLevel = Handoff.sourceNativeSZZHessianHandoffCompilerLevel

round68PublishedSZZPoincareArithmeticLevel : ProofLevel
round68PublishedSZZPoincareArithmeticLevel = SZZ.configuredSU2PoincareCoefficientExactLevel
  where
    configuredSU2PoincareCoefficientExactLevel : ProofLevel
    configuredSU2PoincareCoefficientExactLevel = machineChecked

round68GaugeInvariantCovarianceTransportLevel : ProofLevel
round68GaugeInvariantCovarianceTransportLevel =
  GaugeFix.gaugeInvariantExpectationTransportAlgebraLevel

round68SignedFourthCumulantLevel : ProofLevel
round68SignedFourthCumulantLevel = Cumulant.fourthCumulantSignedMomentCompilerLevel

round68SameLimitMarginTransportLevel : ProofLevel
round68SameLimitMarginTransportLevel = Margin.sameContinuumErrorMarginTransportLevel

round68TransferGapClusteringCompilerLevel : ProofLevel
round68TransferGapClusteringCompilerLevel =
  GapCluster.transferGapToObservableClusteringCompilerLevel

round68LocalOPECompilerLevel : ProofLevel
round68LocalOPECompilerLevel = Local.operemainderModulusCompilerLevel

round68CompactSimpleCoverageLevel : ProofLevel
round68CompactSimpleCoverageLevel = Groups.compactSimpleClassificationEliminationLevel

------------------------------------------------------------------------
-- LIVE ANALYTIC FRONTIER AFTER ROUND68
--
-- The principal new coupling between formerly separate theorem roles is:
--
--   weak-coupling RG beta lower bound
--        + SAME effective-density Wilson coefficient identification
--        + unified-norm Hessian bound on the irrelevant remainder
--        + crossover before the source-native RG validity window closes
--      ---------------------------------------------------------------
--        positive coarse Bakry--Emery margin on the actual effective action.
--
-- The SZZ Poincare/commutator machinery can then supply the terminal spatial
-- gap.  Thus a terminal/reference gap need not be attacked independently if
-- this handoff is completed.
------------------------------------------------------------------------

round68PhysicalHistoryDependentBetaEnclosureLevel : ProofLevel
round68PhysicalHistoryDependentBetaEnclosureLevel =
  Flow.ym4PhysicalHistoryDependentBetaEnclosureLevel

round68PhysicalUnifiedNormLevel : ProofLevel
round68PhysicalUnifiedNormLevel = Unified.physicalUnifiedPolymerNormProducerLevel

round68PhysicalSourceNativeSZZHessianHandoffLevel : ProofLevel
round68PhysicalSourceNativeSZZHessianHandoffLevel =
  Handoff.physicalSourceNativeSZZHessianHandoffLevel

round68PhysicalLocalOPEStressLevel : ProofLevel
round68PhysicalLocalOPEStressLevel = Local.physicalContinuumLocalOperatorOPEStressTensorLevel

round68PhysicalFiniteFourthCumulantLevel : ProofLevel
round68PhysicalFiniteFourthCumulantLevel = Cumulant.physicalFiniteFourPointLowerLevel

round68PhysicalTopDownClayInstantiationLevel : ProofLevel
round68PhysicalTopDownClayInstantiationLevel = conditional
