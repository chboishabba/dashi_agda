module DASHI.ComputerScience.RSA260RHConsumerIndexedUntanglingRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ConsumerIndexedUntanglingTowerExact as Tower
import DASHI.Core.ConsumerIndexedResidualLocalizationExact as Localization
import DASHI.ComputerScience.RSA260BidiConsumerIndexedUntanglingTowerExact as RSA
import DASHI.ComputerScience.RSA260BidiHybridTailCostShapeCollisionExact as CostCollision
import DASHI.ComputerScience.RSA260BidiFactorLayerStructureCollisionExact as FactorCollision
import DASHI.ComputerScience.RSA260BidiRawModeRankResidualLocalizationExact as RawLocalization
import DASHI.ComputerScience.RSA260BidiSparseRawRankObserverFrontierExact as SparseRaw
import DASHI.ComputerScience.RSA260BidiSparseRawRankStressFrontierExact as StressRaw
import DASHI.Analysis.RiemannG2ConsumerIndexedUntanglingTowerExact as RH
import DASHI.Analysis.RiemannG2LiteralPhaseModulationWeldExact as RHWeld
import DASHI.Analysis.RiemannG2PhaseResidualRealizationExact as RHRealization
import DASHI.Analysis.RiemannG2PhaseWeldCellResponseTransportExact as RHExactTransport
import DASHI.Analysis.RiemannG2PhaseWeldCellwiseUpperBridgeExact as RHUpper
import DASHI.ComputerScience.RSA260ProductionSubstitutionRoadmapExact as Production

------------------------------------------------------------------------
-- RSA-260 / RH CONSUMER-INDEXED UNTANGLING ROADMAP
--
-- INFORMATION DESCENT
--   collide -> retain residual -> localize residual -> prune coordinates ->
--   adversarially attack the smaller observer again.
--
-- SEMANTIC ASCENT
--   localized coordinate -> same-object realization -> weakest downstream
--   consequence sufficient for the active consumer -> aggregate consumer.
--
-- The repo-native ConsumerRelativeReduction kernel already distinguishes
-- consumer-preserving reduction, candidate-reduction failure/fidelity escalation,
-- and external target realization.  The tower/localization layer specializes
-- those patterns to recursively retained fibres rather than replacing them.
------------------------------------------------------------------------

coreTowerBoundary : Tower.ConsumerIndexedUntanglingTowerBoundary
coreTowerBoundary = Tower.canonicalConsumerIndexedUntanglingTowerBoundary

coreLocalizationBoundary : Localization.ConsumerIndexedResidualLocalizationBoundary
coreLocalizationBoundary = Localization.canonicalConsumerIndexedResidualLocalizationBoundary

rsaTowerBoundary : RSA.RSAConsumerIndexedUntanglingBoundary
rsaTowerBoundary = RSA.canonicalRSAConsumerIndexedUntanglingBoundary

rsaCostCollisionBoundary : CostCollision.HybridTailCostShapeCollisionBoundary
rsaCostCollisionBoundary = CostCollision.canonicalHybridTailCostShapeCollisionBoundary

rsaFactorCollisionBoundary : FactorCollision.FactorLayerStructureCollisionBoundary
rsaFactorCollisionBoundary = FactorCollision.canonicalFactorLayerStructureCollisionBoundary

rsaRawLocalizationBoundary : RawLocalization.RawModeRankResidualLocalizationBoundary
rsaRawLocalizationBoundary = RawLocalization.canonicalRawModeRankResidualLocalizationBoundary

rsaSparseBoundary : SparseRaw.SparseRawRankObserverFrontierBoundary
rsaSparseBoundary = SparseRaw.canonicalSparseRawRankObserverFrontierBoundary

rsaStressBoundary : StressRaw.SparseRawRankStressFrontierBoundary
rsaStressBoundary = StressRaw.canonicalSparseRawRankStressFrontierBoundary

rhTowerBoundary : RH.RHConsumerIndexedUntanglingBoundary
rhTowerBoundary = RH.canonicalRHConsumerIndexedUntanglingBoundary

rhWeldBoundary : RHWeld.LiteralPhaseModulationWeldBoundary
rhWeldBoundary = RHWeld.canonicalLiteralPhaseModulationWeldBoundary

rhRealizationBoundary : RHRealization.PhaseResidualRealizationBoundary
rhRealizationBoundary = RHRealization.canonicalPhaseResidualRealizationBoundary

rhExactTransportBoundary : RHExactTransport.PhaseWeldCellResponseTransportBoundary
rhExactTransportBoundary = RHExactTransport.canonicalPhaseWeldCellResponseTransportBoundary

rhUpperBoundary : RHUpper.PhaseWeldCellwiseUpperBridgeBoundary
rhUpperBoundary = RHUpper.canonicalPhaseWeldCellwiseUpperBridgeBoundary

productionFirstResidual : Production.ProductionResidual
productionFirstResidual = Production.firstUnpaidProductionResidual

------------------------------------------------------------------------
-- RSA research queue.
--
-- 18-world stage:
--   (degree,r2,r4,r10) separated every then-current receipt.
--
-- Stress with eight fresh seed worlds:
--   the same observer collides on seed7/seed8/seed11/seed14 at (16,7,6,7).
--   Exhaustive runtime subset search over ranks 0..15 finds no degree + <=3
--   rank observer on the 26-world family.  A selected four-rank raw-mode set
--
--     (degree,r4,r5,r7,r9)
--
--   separates all 26 formally.  The first contiguous F2-prefix that survives
--   requires five ranks F2..F6.  Continue attacking the sparse four-rank code;
--   do not call runtime subset minimality a kernel theorem.
------------------------------------------------------------------------

data ResearchUntanglingTarget : Set where
  attackSelectedFourRankObserverWithFreshAdapters : ResearchUntanglingTarget
  compareSixRuntimeMinimalFourRankSetsOnAcquisitionCost : ResearchUntanglingTarget
  formallyAttackAllDegreePlusThreeRankSubsets : ResearchUntanglingTarget
  testSparseObserverAgainstNonReceiptConsumers : ResearchUntanglingTarget
  refineSparseRanksIntoRowSpaceAndPayloadResidual : ResearchUntanglingTarget
  retainExactReplayTailSeparately : ResearchUntanglingTarget

firstResearchUntanglingTarget : ResearchUntanglingTarget
firstResearchUntanglingTarget = attackSelectedFourRankObserverWithFreshAdapters

------------------------------------------------------------------------
-- Production queue: independent execution from a same-object fine carrier.
------------------------------------------------------------------------

data ProductionReconstructionTarget : Set where
  acquireSameObjectFineIncidenceBearingLACarrier : ProductionReconstructionTarget
  authenticateSameObjectBalancingAndPreparation : ProductionReconstructionTarget
  executeIndependentKrylovProjection : ProductionReconstructionTarget
  recoverIndependentGeneratorResidual : ProductionReconstructionTarget
  replayIndependentMksol : ProductionReconstructionTarget
  verifyIndependentNonzeroKernel : ProductionReconstructionTarget
  compileFactorCertificate : ProductionReconstructionTarget

firstProductionReconstructionTarget : ProductionReconstructionTarget
firstProductionReconstructionTarget = acquireSameObjectFineIncidenceBearingLACarrier

------------------------------------------------------------------------
-- RH analytic queue.
--
-- Strong route:
--   same-object weld -> exact aggregation congruence -> exact final-near rewrite.
--
-- Pareto-preferred current-consumer route:
--   same-object weld -> phase-sensitive pointwise majorant -> pair-specific
--   integral monotonicity -> certified cell upper -> existing finite enumerated
--   additive monotonicity -> final near upper -> strict near/far consumer margin.
--
-- Thus exact integrate/finiteNearSum congruence is optional for the upper-bound
-- consumer, although still useful as a stronger representation certificate.
------------------------------------------------------------------------

data RHAnalyticRefinementTarget : Set where
  inhabitUniversalPoleQuotientPhaseModulationWeld : RHAnalyticRefinementTarget
  constructPhaseSensitivePointwiseMajorant : RHAnalyticRefinementTarget
  provePairSpecificIntegralMonotonicity : RHAnalyticRefinementTarget
  certifyIntegratedMajorantCellUppers : RHAnalyticRefinementTarget
  instantiateExactFiniteNearEnumeration : RHAnalyticRefinementTarget
  compileOneSidedFinalNearUpper : RHAnalyticRefinementTarget
  payStrictNearComplementConsumerMargin : RHAnalyticRefinementTarget
  optionalProveExactAggregationCongruence : RHAnalyticRefinementTarget
  closeOnlyThenPromoteRHTerminal : RHAnalyticRefinementTarget

firstRHAnalyticRefinementTarget : RHAnalyticRefinementTarget
firstRHAnalyticRefinementTarget = inhabitUniversalPoleQuotientPhaseModulationWeld

------------------------------------------------------------------------
-- Pareto interpretation.
------------------------------------------------------------------------

record RSA260RHUntanglingRoadmapBoundary : Set where
  constructor rsa260-rh-untangling-roadmap-boundary
  field
    genericConsumerIndexedTowerPaid : Bool
    genericResidualLocalizationPaid : Bool

    priorSparseDegreeR2R4R10SeparatedEighteen : Bool
    priorSparseObserverFailsFreshSeedStress : Bool
    explicitSeed7Seed8StressCollisionPaid : Bool
    runtimeSearchFindsNoDegreePlusThreeRankObserverOnTwentySix : Bool
    selectedDegreeR4R5R7R9SeparatesTwentySix : Bool
    selectedStressFactorisationPaid : Bool
    firstContiguousStressRepairNeedsFiveRanks : Bool
    runtimeFourRankMinimalityKernelProved : Bool
    selectedSparseObserverReplaysCoefficients : Bool
    exactReplayTailStillRetainedSeparately : Bool

    rhFinitePhaseLocalized : Bool
    rhLiteralPhaseWeldInterfaceWritten : Bool
    rhExactAggregationTransportCompilerWritten : Bool
    rhOneSidedCellUpperBridgeWritten : Bool
    exactIntegrationCongruenceRequiredForCurrentUpperConsumer : Bool
    exactFiniteSumCongruenceRequiredForCurrentUpperConsumer : Bool
    rhPhaseSensitiveMajorantAuthorityPaid : Bool
    rhActualUniversalPoleQuotientWeldPaid : Bool
    rhStrictNearComplementMarginPaid : Bool

    productionSearchForUnpublishedIntermediateBytesRequired : Bool
    productionSubstitutionReturnsToFineIncidenceMatrixCarrier : Bool
    independentArtifactsAreHistoricalWithheldArtifacts : Bool

    adequacyMustPrecedeParetoRanking : Bool
    weakerConsumerSufficientRoutePreferredWhenAvailable : Bool
    threeQueuesMayAdvanceIndependently : Bool
open RSA260RHUntanglingRoadmapBoundary public

canonicalRSA260RHUntanglingRoadmapBoundary :
  RSA260RHUntanglingRoadmapBoundary
canonicalRSA260RHUntanglingRoadmapBoundary =
  rsa260-rh-untangling-roadmap-boundary
    true true
    true true true true true true true false false true
    true true true true false false false false false
    false true false
    true true true
