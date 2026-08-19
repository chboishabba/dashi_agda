module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound68TopDownSZZValidation where

------------------------------------------------------------------------
-- ROUND68 FOCUSED ROOT: TOP-DOWN CLAY + BALABAN/SZZ CROSSOVER AUDIT
--
-- No frontier leaf count is authoritative.  Round68 establishes:
--
-- * the five theorem ROLES cover every literal Round67 Clay requirement;
-- * Wilson/SZZ normalization and finite RG crossover are exact;
-- * Wilson+remainder Bakry--Emery positivity is an exact Hessian perturbation;
-- * BUT the UV->IR handoff is valid only if the rigorous source windows overlap.
--
-- Thus SZZ is a conditional shorter producer of the terminal mass-gap role,
-- not an automatic elimination of that role.  If the Bałaban active threshold
-- lies above the SZZ window, the programme must prove additional intermediate-
-- coupling RG/Hessian control instead of silently crossing the gap.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.BalabanPublishedUVStabilityNonlinearRGCoreExact as UV
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.YangMills.BalabanUnifiedPolymerSchwingerNormExact as Unified
import DASHI.Physics.YangMills.BalabanSZZWilsonCrossoverTerminalGapExact as Cross
import DASHI.Physics.YangMills.BalabanSZZHessianPerturbationExact as Hess
import DASHI.Physics.YangMills.BalabanSZZSourceNativeHessianHandoffExact as Handoff
import DASHI.Physics.YangMills.BalabanSZZActiveWindowOverlapNecessaryExact as Overlap
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

round68WindowOverlapNecessityLevel : ProofLevel
round68WindowOverlapNecessityLevel = Overlap.balabanSZZWindowOverlapNecessityLevel

round68PublishedSZZPoincareArithmeticLevel : ProofLevel
round68PublishedSZZPoincareArithmeticLevel = machineChecked

round68GaugeInvariantCovarianceTransportLevel : ProofLevel
round68GaugeInvariantCovarianceTransportLevel =
  GaugeFix.gaugeInvariantExpectationTransportAlgebraLevel

round68SignedFourthCumulantLevel : ProofLevel
round68SignedFourthCumulantLevel = Cumulant.fourthCumulantSignedMomentCompilerLevel

round68SameLimitMarginTransportLevel : ProofLevel
round68SameLimitMarginTransportLevel = Margin.sameLimitEndpointMarginTransportLevel

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
-- For the SZZ shortcut to discharge the terminal spectral input, prove:
--
--   (A) a source-valid active scale reaches the SZZ inverse-coupling window;
--   (B) the SAME CMP119/CMP122 effective density is Wilson(u_n)+R_n;
--   (C) the unified norm bounds Hess R_n by rho_n;
--   (D) K_W(u_n)-rho_n > 0.
--
-- If (A) fails for the published Bałaban small-coupling threshold, replace it
-- by a new intermediate-coupling RG/Hessian theorem.  Nothing in this root
-- promotes fixed-spacing strong-coupling clustering directly to Clay.
------------------------------------------------------------------------

round68PhysicalHistoryDependentBetaEnclosureLevel : ProofLevel
round68PhysicalHistoryDependentBetaEnclosureLevel =
  Flow.ym4PhysicalHistoryDependentBetaEnclosureLevel

round68PhysicalUnifiedNormLevel : ProofLevel
round68PhysicalUnifiedNormLevel = Unified.physicalYMUnifiedPolymerNormProducerLevel

round68PhysicalSourceWindowOverlapLevel : ProofLevel
round68PhysicalSourceWindowOverlapLevel = Overlap.physicalBalabanSZZWindowOverlapLevel

round68PhysicalSourceNativeSZZHessianHandoffLevel : ProofLevel
round68PhysicalSourceNativeSZZHessianHandoffLevel =
  Handoff.physicalSourceNativeSZZHessianHandoffLevel

round68PhysicalLocalOPEStressLevel : ProofLevel
round68PhysicalLocalOPEStressLevel = Local.physicalContinuumLocalOperatorOPEStressTensorLevel

round68PhysicalFiniteFourthCumulantLevel : ProofLevel
round68PhysicalFiniteFourthCumulantLevel = Cumulant.physicalFiniteFourPointLowerLevel

round68PhysicalTopDownClayInstantiationLevel : ProofLevel
round68PhysicalTopDownClayInstantiationLevel = conditional
