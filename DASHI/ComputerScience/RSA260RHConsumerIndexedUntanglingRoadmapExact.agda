module DASHI.ComputerScience.RSA260RHConsumerIndexedUntanglingRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ConsumerIndexedUntanglingTowerExact as Tower
import DASHI.ComputerScience.RSA260BidiConsumerIndexedUntanglingTowerExact as RSA
import DASHI.ComputerScience.RSA260BidiHybridTailCostShapeCollisionExact as CostCollision
import DASHI.ComputerScience.RSA260BidiFactorLayerStructureCollisionExact as FactorCollision
import DASHI.Analysis.RiemannG2ConsumerIndexedUntanglingTowerExact as RH
import DASHI.Analysis.RiemannG2LiteralPhaseModulationWeldExact as RHWeld
import DASHI.ComputerScience.RSA260ProductionSubstitutionRoadmapExact as Production

------------------------------------------------------------------------
-- RSA-260 / RH CONSUMER-INDEXED UNTANGLING ROADMAP
--
-- Three queues remain explicit and non-blocking:
--
--   (A) recursive untangling research
--       projection collision -> missing coordinate -> retained residual ->
--       strict refinement -> repeat until consumer terminal or exact terminal;
--
--   (B) RSA production reconstruction
--       published execution constraints -> same-object fine-incidence/matrix
--       carrier -> independently execute Krylov/lingen/mksol -> kernel -> factor;
--
--   (C) RH analytic refinement
--       coarse count/envelope collision -> phase-sensitive residual -> literal
--       target-relative model -> same-carrier translation/modulation weld ->
--       strict consumer margin.
--
-- New frontier information:
--
-- * RSA: rotate3/affine7 collide not only on codec cost shape but on the entire
--   current factor-mode basis/mask footprint (layers 0,1,16). The next retained
--   residual is therefore the complementary raw-mode layer payload, which must
--   itself be factorized and attacked rather than accepted as globally minimal.
--
-- * RH: proof-relevant phase laws and the literal near-cell kernel now have an
--   explicit weld interface. The live theorem is to inhabit that interface on
--   the actual universal pole-quotient analytic carrier; merely identifying the
--   missing phase coordinate is no longer the sharp frontier.
------------------------------------------------------------------------

coreTowerBoundary : Tower.ConsumerIndexedUntanglingTowerBoundary
coreTowerBoundary = Tower.canonicalConsumerIndexedUntanglingTowerBoundary

rsaTowerBoundary : RSA.RSAConsumerIndexedUntanglingBoundary
rsaTowerBoundary = RSA.canonicalRSAConsumerIndexedUntanglingBoundary

rsaCostCollisionBoundary : CostCollision.HybridTailCostShapeCollisionBoundary
rsaCostCollisionBoundary = CostCollision.canonicalHybridTailCostShapeCollisionBoundary

rsaFactorCollisionBoundary : FactorCollision.FactorLayerStructureCollisionBoundary
rsaFactorCollisionBoundary = FactorCollision.canonicalFactorLayerStructureCollisionBoundary

rhTowerBoundary : RH.RHConsumerIndexedUntanglingBoundary
rhTowerBoundary = RH.canonicalRHConsumerIndexedUntanglingBoundary

rhWeldBoundary : RHWeld.LiteralPhaseModulationWeldBoundary
rhWeldBoundary = RHWeld.canonicalLiteralPhaseModulationWeldBoundary

productionFirstResidual : Production.ProductionResidual
productionFirstResidual = Production.firstUnpaidProductionResidual

------------------------------------------------------------------------
-- Research queue: the current tail has now been attacked twice.
------------------------------------------------------------------------

data ResearchUntanglingTarget : Set where
  factorRawModePayloadBelowFactorStructureCollision : ResearchUntanglingTarget
  adversariallyAttackEveryProposedRSAQuotient : ResearchUntanglingTarget
  testWhetherSomeRawLayersAreConsumerIrrelevant : ResearchUntanglingTarget
  deriveConsumerTerminalBeforeExactTerminalWhenPossible : ResearchUntanglingTarget
  separateDescriptionWitnessExecutionCosts : ResearchUntanglingTarget
  transportOnlyGenericUntanglingStructureIntoRH : ResearchUntanglingTarget

firstResearchUntanglingTarget : ResearchUntanglingTarget
firstResearchUntanglingTarget = factorRawModePayloadBelowFactorStructureCollision

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
-- RH queue: phase coordinate found; now inhabit the same-carrier weld.
------------------------------------------------------------------------

data RHAnalyticRefinementTarget : Set where
  inhabitUniversalPoleQuotientPhaseModulationWeld : RHAnalyticRefinementTarget
  bindLiteralScalarFrequencyOrdinatePhaseCarriers : RHAnalyticRefinementTarget
  proveEvenProjectionEqualsLiteralCosineKernel : RHAnalyticRefinementTarget
  pushWeldThroughLiteralCellResponse : RHAnalyticRefinementTarget
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
    rsaFiniteExactTowerPaid : Bool
    rsaFullCostShapeCollisionPaid : Bool
    rsaFactorLayerStructureCollisionPaid : Bool
    rawModePayloadIsNextRSAResidual : Bool
    rawModePayloadProvedGloballyMinimal : Bool
    rhFiniteCollisionRefinementPaid : Bool
    rhLiteralPhaseWeldInterfaceWritten : Bool
    rhActualUniversalPoleQuotientWeldPaid : Bool
    researchShouldContinueBelowCurrentRSAResidual : Bool
    productionSearchForUnpublishedIntermediateBytesRequired : Bool
    productionSubstitutionReturnsToFineIncidenceMatrixCarrier : Bool
    publishedRunEnvelopeUsedAsConstraintSurface : Bool
    independentExecutionMayProduceNewAStarGeneratorMksolArtifacts : Bool
    independentArtifactsAreHistoricalWithheldArtifacts : Bool
    rsaFiniteReplayPaysRHAnalyticRepresentation : Bool
    rhPhaseCoordinateAlonePaysStrictRHMargin : Bool
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
    false
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
    true
    true
