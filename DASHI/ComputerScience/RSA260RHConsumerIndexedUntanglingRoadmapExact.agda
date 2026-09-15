module DASHI.ComputerScience.RSA260RHConsumerIndexedUntanglingRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ConsumerIndexedUntanglingTowerExact as Tower
import DASHI.Core.ConsumerIndexedResidualLocalizationExact as Localization
import DASHI.ComputerScience.RSA260BidiConsumerIndexedUntanglingTowerExact as RSA
import DASHI.ComputerScience.RSA260BidiHybridTailCostShapeCollisionExact as CostCollision
import DASHI.ComputerScience.RSA260BidiFactorLayerStructureCollisionExact as FactorCollision
import DASHI.ComputerScience.RSA260BidiRawModeRankResidualLocalizationExact as RawLocalization
import DASHI.Analysis.RiemannG2ConsumerIndexedUntanglingTowerExact as RH
import DASHI.Analysis.RiemannG2LiteralPhaseModulationWeldExact as RHWeld
import DASHI.Analysis.RiemannG2PhaseResidualRealizationExact as RHRealization
import DASHI.ComputerScience.RSA260ProductionSubstitutionRoadmapExact as Production

------------------------------------------------------------------------
-- RSA-260 / RH CONSUMER-INDEXED UNTANGLING ROADMAP
--
-- Three queues remain explicit and non-blocking:
--
--   (A) recursive untangling research;
--   (B) RSA production reconstruction from a same-object fine carrier;
--   (C) RH analytic refinement on the literal pole-quotient carrier.
--
-- The common tower now has a second generic operation: residual localization.
-- Once a coarse collision proves that RelativeFine matters, do not automatically
-- retain the whole residual.  Search a smaller observer on RelativeFine and
-- prove that it still separates the concrete consumer witness.
--
-- Current RSA descent:
--
--   whole generator
--     -> rank prefix + hybrid tail
--     -> codec-cost collision
--     -> identical factor basis/mask structure
--     -> raw-mode residual
--     -> first raw layer rank(F_2) separates rotate3/affine7 (7 vs 5).
--
-- Therefore full raw payload is not required merely to separate that witness.
-- The new research frontier is to attack this localized raw-rank coordinate on
-- a wider collision family and refine again if it fails.
--
-- Current RH descent:
--
--   count/envelope collision
--     -> signed target-relative phase residual
--     -> finite phase class localizes the consumer witness
--     -> same-object analytic weld must realize that phase as the literal
--        target-gap/cosine equality on the universal pole-quotient carrier.
--
-- Finite localization does not pay the analytic weld, near budget, or RH.
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

rhTowerBoundary : RH.RHConsumerIndexedUntanglingBoundary
rhTowerBoundary = RH.canonicalRHConsumerIndexedUntanglingBoundary

rhWeldBoundary : RHWeld.LiteralPhaseModulationWeldBoundary
rhWeldBoundary = RHWeld.canonicalLiteralPhaseModulationWeldBoundary

rhRealizationBoundary : RHRealization.PhaseResidualRealizationBoundary
rhRealizationBoundary = RHRealization.canonicalPhaseResidualRealizationBoundary

productionFirstResidual : Production.ProductionResidual
productionFirstResidual = Production.firstUnpaidProductionResidual

------------------------------------------------------------------------
-- Research queue: attack the newly localized RSA coordinate.
------------------------------------------------------------------------

data ResearchUntanglingTarget : Set where
  attackLocalizedRawRankAcrossWiderCollisionFamily : ResearchUntanglingTarget
  refineRawRankIntoRowSpaceAndPayloadResidual : ResearchUntanglingTarget
  adversariallyAttackEveryProposedRSAQuotient : ResearchUntanglingTarget
  deriveConsumerTerminalBeforeExactTerminalWhenPossible : ResearchUntanglingTarget
  separateDescriptionWitnessExecutionCosts : ResearchUntanglingTarget
  transportOnlyGenericUntanglingStructureIntoRH : ResearchUntanglingTarget

firstResearchUntanglingTarget : ResearchUntanglingTarget
firstResearchUntanglingTarget = attackLocalizedRawRankAcrossWiderCollisionFamily

------------------------------------------------------------------------
-- Production queue: historical A*/F.sols custody is not assumed available.
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
-- RH queue: localized phase found; now realize it on the literal carrier.
------------------------------------------------------------------------

data RHAnalyticRefinementTarget : Set where
  inhabitUniversalPoleQuotientPhaseModulationWeld : RHAnalyticRefinementTarget
  bindLiteralScalarFrequencyOrdinatePhaseCarriers : RHAnalyticRefinementTarget
  proveEvenProjectionEqualsLiteralCosineKernel : RHAnalyticRefinementTarget
  pushWeldThroughLiteralCellResponse : RHAnalyticRefinementTarget
  aggregateLiteralCellsOverFiniteNearSum : RHAnalyticRefinementTarget
  deriveFiniteNearConsumerBudget : RHAnalyticRefinementTarget
  payStrictNearComplementConsumerMargin : RHAnalyticRefinementTarget
  closeOnlyThenPromoteRHTerminal : RHAnalyticRefinementTarget

firstRHAnalyticRefinementTarget : RHAnalyticRefinementTarget
firstRHAnalyticRefinementTarget = inhabitUniversalPoleQuotientPhaseModulationWeld

------------------------------------------------------------------------
-- Pareto interpretation.
------------------------------------------------------------------------

data GlobalLane : Set where
  recursiveUntanglingResearch : GlobalLane
  rsaProductionReconstruction : GlobalLane
  rhAnalyticRefinement : GlobalLane

record RSA260RHUntanglingRoadmapBoundary : Set where
  constructor rsa260-rh-untangling-roadmap-boundary
  field
    genericConsumerIndexedTowerPaid : Bool
    genericResidualLocalizationPaid : Bool
    rsaFiniteExactTowerPaid : Bool
    rsaFullCostShapeCollisionPaid : Bool
    rsaFactorLayerStructureCollisionPaid : Bool
    rsaFirstRawLayerRankLocalizesCurrentWitness : Bool
    fullRawPayloadRequiredToSeparateCurrentWitness : Bool
    firstRawRankGloballyAdequate : Bool
    firstRawRankGloballyMinimal : Bool
    rhFiniteCollisionRefinementPaid : Bool
    rhFinitePhaseLocalized : Bool
    rhLiteralPhaseWeldInterfaceWritten : Bool
    rhConditionalAnalyticRealizationCompilerWritten : Bool
    rhActualUniversalPoleQuotientWeldPaid : Bool
    researchShouldContinueBelowCurrentRSAResidual : Bool
    productionSearchForUnpublishedIntermediateBytesRequired : Bool
    productionSubstitutionReturnsToFineIncidenceMatrixCarrier : Bool
    publishedRunEnvelopeUsedAsConstraintSurface : Bool
    independentExecutionMayProduceNewAStarGeneratorMksolArtifacts : Bool
    independentArtifactsAreHistoricalWithheldArtifacts : Bool
    rsaFiniteReplayPaysRHAnalyticRepresentation : Bool
    rhFinitePhaseLocalizationPaysStrictRHMargin : Bool
    adequacyMustPrecedeParetoRanking : Bool
    threeQueuesMayAdvanceIndependently : Bool
open RSA260RHUntanglingRoadmapBoundary public

canonicalRSA260RHUntanglingRoadmapBoundary :
  RSA260RHUntanglingRoadmapBoundary
canonicalRSA260RHUntanglingRoadmapBoundary =
  rsa260-rh-untangling-roadmap-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false
    true
    true
    true
    true
    false
    true
    false
    true
    true
    true
    false
    false
    false
    false
    true
    true
