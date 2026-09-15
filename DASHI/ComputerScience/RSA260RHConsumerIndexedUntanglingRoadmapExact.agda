module DASHI.ComputerScience.RSA260RHConsumerIndexedUntanglingRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ConsumerIndexedUntanglingTowerExact as Tower
import DASHI.Core.ConsumerIndexedResidualLocalizationExact as Localization
import DASHI.ComputerScience.RSA260BidiConsumerIndexedUntanglingTowerExact as RSA
import DASHI.ComputerScience.RSA260BidiHybridTailCostShapeCollisionExact as CostCollision
import DASHI.ComputerScience.RSA260BidiFactorLayerStructureCollisionExact as FactorCollision
import DASHI.ComputerScience.RSA260BidiRawModeRankResidualLocalizationExact as RawLocalization
import DASHI.ComputerScience.RSA260BidiRawRankPrefixFrontierExact as RawFrontier
import DASHI.ComputerScience.RSA260BidiDegreeRawRankMinimalFrontierExact as MinimalRaw
import DASHI.ComputerScience.RSA260BidiRawRankCrossValidationAcquisitionExact as RawAcquisition
import DASHI.Analysis.RiemannG2ConsumerIndexedUntanglingTowerExact as RH
import DASHI.Analysis.RiemannG2LiteralPhaseModulationWeldExact as RHWeld
import DASHI.Analysis.RiemannG2PhaseResidualRealizationExact as RHRealization
import DASHI.Analysis.RiemannG2PhaseWeldCellResponseTransportExact as RHTransport
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
-- The shared research calculus now has two operations:
--   1. exact recursive reopening through a tower of coarse/residual fibres;
--   2. consumer-indexed residual localization, allowing a retained residual to
--      be observed more coarsely and attacked again before it is kept wholesale.
--
-- RSA frontier:
--
--   whole generator
--     -> rank prefix + hybrid replay tail
--     -> codec-cost collision
--     -> identical factor basis/mask structure
--     -> raw-mode residual
--     -> rank(F2) separates rotate3/affine7
--     -> (r2,r3,r4) still collides
--     -> (degree,r2,r3,r4) separates the ten current receipt identities
--     -> degree+one and degree+two raw ranks still collide.
--
-- Hence three raw ranks are the first separating CHECKED contiguous raw prefix
-- from F2 once degree is retained.  That is not global minimality.  The next
-- payment is cross-validation on independent seed runs; the existing 12-run
-- codec receipt does not retain per-run degree/r2/r3/r4 coordinates, so those
-- coordinates must be reacquired rather than inferred from aggregate metrics.
--
-- RH frontier:
--
--   count/envelope collision
--     -> signed target-relative phase residual
--     -> finite phase class localizes the witness
--     -> same-object phase/modulation weld realizes target gap + literal cosine
--     -> integration congruence transports pointwise equality through cellResponse
--     -> finite-sum congruence transports cell equality through finiteNearSum
--     -> final nearResponseAt(J) equality.
--
-- The last three arrows are now compiler output CONDITIONALLY on an inhabited
-- same-object weld plus explicit congruence laws.  The current literal kernel
-- interface carries neither aggregation congruence law, so no strict near budget
-- or RH terminal is promoted here.
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

rsaRawFrontierBoundary : RawFrontier.RawRankPrefixFrontierBoundary
rsaRawFrontierBoundary = RawFrontier.canonicalRawRankPrefixFrontierBoundary

rsaMinimalRawBoundary : MinimalRaw.DegreeRawRankMinimalFrontierBoundary
rsaMinimalRawBoundary = MinimalRaw.canonicalDegreeRawRankMinimalFrontierBoundary

rsaRawAcquisitionBoundary : RawAcquisition.RawRankCrossValidationAcquisitionBoundary
rsaRawAcquisitionBoundary = RawAcquisition.canonicalRawRankCrossValidationAcquisitionBoundary

rhTowerBoundary : RH.RHConsumerIndexedUntanglingBoundary
rhTowerBoundary = RH.canonicalRHConsumerIndexedUntanglingBoundary

rhWeldBoundary : RHWeld.LiteralPhaseModulationWeldBoundary
rhWeldBoundary = RHWeld.canonicalLiteralPhaseModulationWeldBoundary

rhRealizationBoundary : RHRealization.PhaseResidualRealizationBoundary
rhRealizationBoundary = RHRealization.canonicalPhaseResidualRealizationBoundary

rhTransportBoundary : RHTransport.PhaseWeldCellResponseTransportBoundary
rhTransportBoundary = RHTransport.canonicalPhaseWeldCellResponseTransportBoundary

productionFirstResidual : Production.ProductionResidual
productionFirstResidual = Production.firstUnpaidProductionResidual

------------------------------------------------------------------------
-- Research queue: validate the smaller observer before claiming a terminal.
------------------------------------------------------------------------

data ResearchUntanglingTarget : Set where
  reacquireIndependentSeedDegreeRawRanks : ResearchUntanglingTarget
  crossValidateDegreeRawRanksOnIndependentSeedPortfolio : ResearchUntanglingTarget
  attackNonContiguousSubsetsOfCurrentRawRanks : ResearchUntanglingTarget
  refineRawRankIntoRowSpaceAndPayloadResidual : ResearchUntanglingTarget
  adversariallyAttackEveryProposedRSAQuotient : ResearchUntanglingTarget
  deriveConsumerTerminalBeforeExactTerminalWhenPossible : ResearchUntanglingTarget

firstResearchUntanglingTarget : ResearchUntanglingTarget
firstResearchUntanglingTarget = reacquireIndependentSeedDegreeRawRanks

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
-- RH queue: same-object realization first, then aggregation laws.
------------------------------------------------------------------------

data RHAnalyticRefinementTarget : Set where
  inhabitUniversalPoleQuotientPhaseModulationWeld : RHAnalyticRefinementTarget
  proveLiteralIntegrationCongruence : RHAnalyticRefinementTarget
  proveLiteralFiniteNearSumCongruence : RHAnalyticRefinementTarget
  compilePhaseThroughLiteralCellResponse : RHAnalyticRefinementTarget
  compilePhaseThroughFiniteNearSum : RHAnalyticRefinementTarget
  deriveFiniteNearConsumerBudget : RHAnalyticRefinementTarget
  payStrictNearComplementConsumerMargin : RHAnalyticRefinementTarget
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
    degreePlusOneRawRankStillCollides : Bool
    degreePlusTwoRawRanksStillCollide : Bool
    degreePlusThreeRawRanksSeparateCurrentTen : Bool
    threeRawRanksFirstSeparatingCheckedContiguousPrefix : Bool
    degreePlusThreeRawRanksGloballyMinimal : Bool
    independentSeedPerRunRawRanksRetained : Bool
    independentSeedRawRankCrossValidationPaid : Bool
    exactReplayTailStillRetainedSeparately : Bool
    rhFinitePhaseLocalized : Bool
    rhLiteralPhaseWeldInterfaceWritten : Bool
    rhConditionalCellAndFiniteNearTransportCompilerWritten : Bool
    rhActualUniversalPoleQuotientWeldPaid : Bool
    rhIntegrationCongruencePaid : Bool
    rhFiniteNearSumCongruencePaid : Bool
    rhNumericNearBudgetPaid : Bool
    productionSearchForUnpublishedIntermediateBytesRequired : Bool
    productionSubstitutionReturnsToFineIncidenceMatrixCarrier : Bool
    independentArtifactsAreHistoricalWithheldArtifacts : Bool
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
    false
    false
    false
    false
    true
    false
    true
    true
