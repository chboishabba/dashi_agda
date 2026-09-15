module DASHI.ComputerScience.RSA260RHConsumerIndexedUntanglingRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ConsumerIndexedUntanglingTowerExact as Tower
import DASHI.Core.ConsumerIndexedResidualLocalizationExact as Localization
import DASHI.ComputerScience.RSA260BidiConsumerIndexedUntanglingTowerExact as RSA
import DASHI.ComputerScience.RSA260BidiHybridTailCostShapeCollisionExact as CostCollision
import DASHI.ComputerScience.RSA260BidiFactorLayerStructureCollisionExact as FactorCollision
import DASHI.ComputerScience.RSA260BidiRawModeRankResidualLocalizationExact as RawLocalization
import DASHI.ComputerScience.RSA260BidiDegreeRawRankMinimalFrontierExact as MinimalRaw
import DASHI.ComputerScience.RSA260BidiSparseRawRankObserverFrontierExact as SparseRaw
import DASHI.Analysis.RiemannG2ConsumerIndexedUntanglingTowerExact as RH
import DASHI.Analysis.RiemannG2LiteralPhaseModulationWeldExact as RHWeld
import DASHI.Analysis.RiemannG2PhaseResidualRealizationExact as RHRealization
import DASHI.Analysis.RiemannG2PhaseWeldCellResponseTransportExact as RHExactTransport
import DASHI.Analysis.RiemannG2PhaseWeldCellwiseUpperBridgeExact as RHUpper
import DASHI.ComputerScience.RSA260ProductionSubstitutionRoadmapExact as Production

------------------------------------------------------------------------
-- RSA-260 / RH CONSUMER-INDEXED UNTANGLING ROADMAP
--
-- The common programme now has two dual motions.
--
-- INFORMATION DESCENT
--   collide -> retain residual -> localize residual -> prune coordinates ->
--   adversarially attack the smaller observer again.
--
-- SEMANTIC ASCENT
--   localized coordinate -> same-object realization -> weakest downstream
--   consequence sufficient for the active consumer -> aggregate consumer.
--
-- RSA currently demonstrates descent.  RH currently demonstrates ascent.
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

rsaMinimalRawBoundary : MinimalRaw.DegreeRawRankMinimalFrontierBoundary
rsaMinimalRawBoundary = MinimalRaw.canonicalDegreeRawRankMinimalFrontierBoundary

rsaSparseBoundary : SparseRaw.SparseRawRankObserverFrontierBoundary
rsaSparseBoundary = SparseRaw.canonicalSparseRawRankObserverFrontierBoundary

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
-- Independent seeds falsified the ten-world contiguous candidate.  Reacquired
-- data then exposed a sparse 18-world factorisation:
--
--   (degree, rank F2, rank F4, rank F10).
--
-- Runtime exhaustive search found no degree+one-rank or degree+two-rank subset
-- over indices 0..15, but that global two-rank impossibility is not yet an Agda
-- theorem.  Keep exact replay tail orthogonal to the receipt consumer.
------------------------------------------------------------------------

data ResearchUntanglingTarget : Set where
  attackSparseObserverWithNewSeedAndAdapterFamilies : ResearchUntanglingTarget
  formallyAttackAllDegreePlusTwoRankSubsets : ResearchUntanglingTarget
  compareSparseTriplesOnDescriptionAndAcquisitionCost : ResearchUntanglingTarget
  testSparseObserverAgainstNonReceiptConsumers : ResearchUntanglingTarget
  refineSparseRanksIntoRowSpaceAndPayloadResidual : ResearchUntanglingTarget
  retainExactReplayTailSeparately : ResearchUntanglingTarget

firstResearchUntanglingTarget : ResearchUntanglingTarget
firstResearchUntanglingTarget = attackSparseObserverWithNewSeedAndAdapterFamilies

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
-- Two semantic-ascent routes now coexist:
--
--   strong equality route:
--     weld -> integration congruence -> finite-sum congruence -> exact final near;
--
--   consumer-sufficient upper route:
--     weld -> phase-sensitive pointwise majorant -> pair-specific integral
--     monotonicity -> cell upper -> existing finite-fold monotonicity -> final
--     near upper.
--
-- The second route is Pareto-preferred for the current strict-upper consumer.
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

    contiguousDegreeR2R3R4FailsIndependentSeeds : Bool
    sparseDegreeR2R4R10SeparatesCombinedEighteen : Bool
    sparseObserverFormalFactorisationPaid : Bool
    runtimeSearchFoundNoDegreePlusTwoRankObserver : Bool
    allDegreePlusTwoRankImpossibilityKernelProved : Bool
    sparseObserverReplaysCoefficients : Bool
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
    true true true true false false true
    true true true true false false false false false
    false true false
    true true true
