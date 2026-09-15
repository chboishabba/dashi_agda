module DASHI.ComputerScience.RSA260RHConsumerIndexedUntanglingRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ConsumerIndexedUntanglingTowerExact as Tower
import DASHI.ComputerScience.RSA260BidiConsumerIndexedUntanglingTowerExact as RSA
import DASHI.Analysis.RiemannG2ConsumerIndexedUntanglingTowerExact as RH
import DASHI.ComputerScience.RSA260ProductionSubstitutionRoadmapExact as Production

------------------------------------------------------------------------
-- RSA-260 / RH CONSUMER-INDEXED UNTANGLING ROADMAP
--
-- Three queues are now explicit and non-blocking:
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
--       target-relative model -> translation/modulation -> strict consumer margin.
--
-- The queues share Core structure but not empirical or analytic payment. In
-- particular, finite RSA replay does not prove RH and finite RH cell separation
-- does not recover withheld RSA artifacts.
------------------------------------------------------------------------

coreTowerBoundary : Tower.ConsumerIndexedUntanglingTowerBoundary
coreTowerBoundary = Tower.canonicalConsumerIndexedUntanglingTowerBoundary

rsaTowerBoundary : RSA.RSAConsumerIndexedUntanglingBoundary
rsaTowerBoundary = RSA.canonicalRSAConsumerIndexedUntanglingBoundary

rhTowerBoundary : RH.RHConsumerIndexedUntanglingBoundary
rhTowerBoundary = RH.canonicalRHConsumerIndexedUntanglingBoundary

productionFirstResidual : Production.ProductionResidual
productionFirstResidual = Production.firstUnpaidProductionResidual

------------------------------------------------------------------------
-- Research queue: keep attacking residuals rather than stopping at one codec.
------------------------------------------------------------------------

data ResearchUntanglingTarget : Set where
  recursivelyFactorRSAResidualBelowCurrentTail : ResearchUntanglingTarget
  adversariallyAttackEveryProposedRSAQuotient : ResearchUntanglingTarget
  deriveConsumerTerminalBeforeExactTerminalWhenPossible : ResearchUntanglingTarget
  separateDescriptionWitnessExecutionCosts : ResearchUntanglingTarget
  transportOnlyGenericUntanglingStructureIntoRH : ResearchUntanglingTarget

firstResearchUntanglingTarget : ResearchUntanglingTarget
firstResearchUntanglingTarget = recursivelyFactorRSAResidualBelowCurrentTail

------------------------------------------------------------------------
-- Production queue: historical A*/F.sols custody is not assumed available.
-- The canonical production-substitution owner already identifies the earlier
-- same-object fine-incidence/matrix carrier as the first unpaid residual.
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
-- RH queue: same methodology, different terminal theorem.
------------------------------------------------------------------------

data RHAnalyticRefinementTarget : Set where
  realizeProofRelevantTargetRelativePhase : RHAnalyticRefinementTarget
  proveTargetTranslationModulationOnLiteralCarrier : RHAnalyticRefinementTarget
  identifyFinalNearResponseWithLiteralFiniteSum : RHAnalyticRefinementTarget
  payStrictNearComplementConsumerMargin : RHAnalyticRefinementTarget
  closeOnlyThenPromoteRHTerminal : RHAnalyticRefinementTarget

firstRHAnalyticRefinementTarget : RHAnalyticRefinementTarget
firstRHAnalyticRefinementTarget = realizeProofRelevantTargetRelativePhase

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
    rhFiniteCollisionRefinementPaid : Bool
    researchShouldContinueBelowCurrentRSAResidual : Bool
    scalarInvariantAccumulationDominatedWhenConsumerCollisionPersists : Bool
    productionSearchForUnpublishedIntermediateBytesRequired : Bool
    productionSubstitutionReturnsToFineIncidenceMatrixCarrier : Bool
    publishedRunEnvelopeUsedAsConstraintSurface : Bool
    independentExecutionMayProduceNewAStarGeneratorMksolArtifacts : Bool
    independentArtifactsAreHistoricalWithheldArtifacts : Bool
    rhMayReuseGenericUntanglingStructure : Bool
    rsaFiniteReplayPaysRHAnalyticRepresentation : Bool
    rhFiniteCollisionPaysStrictRHMargin : Bool
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
    true
    false
    true
    false
    false
    true
    true
