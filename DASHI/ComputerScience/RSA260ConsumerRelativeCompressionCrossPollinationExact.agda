module DASHI.ComputerScience.RSA260ConsumerRelativeCompressionCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ConsumerRelativeMinimalFidelityExact as Minimal
import DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact as Approx
import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.ComputerScience.RSA260SymmetryCensusOrbitQuotientBidiExact as Bidi
import DASHI.ComputerScience.RSA260ProductionArtifactSubstituteAdmissionExact as Substitute

------------------------------------------------------------------------
-- CONSUMER-RELATIVE COMPRESSION CROSS-POLLINATION FOR RSA-260
--
-- Donor pattern: PR #885 FibreRoutingCompressionLadderExact.
-- Reused core rule: rank only inside the consumer-adequate/admissible stratum.
--
-- This owner deliberately does NOT import the PR #885 branch.  It reuses the
-- shared core MDL / reduction-search owners already present in this branch and
-- instantiates the same rule on the RSA symmetry/replay surface.
------------------------------------------------------------------------

data RSACompressionStage : Set where
  fullWidthStage : RSACompressionStage
  pairOrbitQuotientStage : RSACompressionStage
  aggressiveUncertifiedStage : RSACompressionStage

stageReference : RSACompressionStage → String
stageReference fullWidthStage = "full 256-coordinate synthetic GF(2) carrier"
stageReference pairOrbitQuotientStage = "128-coordinate exact pair-orbit quotient"
stageReference aggressiveUncertifiedStage = "illustrative 64-coordinate further compression candidate"

stageWidth : RSACompressionStage → Nat
stageWidth fullWidthStage = 256
stageWidth pairOrbitQuotientStage = 128
stageWidth aggressiveUncertifiedStage = 64

stageAdmissible : RSACompressionStage → Set
stageAdmissible stage = ⊤

-- Set-sized receipts: only the full carrier and the executed exact quotient are
-- eligible for the exact kernel consumer in the declared finite portfolio.
data ExactKernelAdequacy : RSACompressionStage → Set where
  fullWidthExact : ExactKernelAdequacy fullWidthStage
  pairOrbitExact : ExactKernelAdequacy pairOrbitQuotientStage

stageExactKernelAdequate : RSACompressionStage → Set
stageExactKernelAdequate = ExactKernelAdequacy

data StageRefines : RSACompressionStage → RSACompressionStage → Set where
  fullReflexive : StageRefines fullWidthStage fullWidthStage
  pairReflexive : StageRefines pairOrbitQuotientStage pairOrbitQuotientStage
  aggressiveReflexive : StageRefines aggressiveUncertifiedStage aggressiveUncertifiedStage
  aggressiveToPair : StageRefines aggressiveUncertifiedStage pairOrbitQuotientStage
  pairToFull : StageRefines pairOrbitQuotientStage fullWidthStage

exactKernelCompressionProblem : MDL.ConsumerMDLProblem
exactKernelCompressionProblem =
  MDL.consumerMDLProblem
    RSACompressionStage
    stageAdmissible
    stageExactKernelAdequate
    stageWidth
    StageRefines
    stageReference
    "coordinate width proxy; raw width ranks only after exact consumer adequacy"
    "synthetic exact GF(2) quotient/lift kernel consumer"

fullWidthEligible : MDL.Eligible exactKernelCompressionProblem fullWidthStage
fullWidthEligible = tt , fullWidthExact

pairOrbitEligible : MDL.Eligible exactKernelCompressionProblem pairOrbitQuotientStage
pairOrbitEligible = tt , pairOrbitExact

aggressiveAdequacyImpossible : ExactKernelAdequacy aggressiveUncertifiedStage → ⊥
aggressiveAdequacyImpossible ()

aggressiveNotEligible : MDL.Eligible exactKernelCompressionProblem aggressiveUncertifiedStage → ⊥
aggressiveNotEligible eligible = aggressiveAdequacyImpossible (proj₂ eligible)

data AggressiveFailureWitness : Set where
  aggressiveFailureWitness : AggressiveFailureWitness

aggressiveCounterexample :
  MDL.ConsumerCounterexample exactKernelCompressionProblem aggressiveUncertifiedStage
aggressiveCounterexample =
  MDL.consumerCounterexample
    AggressiveFailureWitness
    aggressiveFailureWitness
    aggressiveAdequacyImpossible
    "candidate deletes structure beyond the currently certified pair-orbit quotient"
    "no exact quotient/lift/intertwining certificate exists for this candidate"

aggressiveLocalRepair :
  MDL.LocalRefinementRepair
    exactKernelCompressionProblem
    aggressiveUncertifiedStage
    pairOrbitQuotientStage
aggressiveLocalRepair =
  MDL.localRefinementRepair
    aggressiveCounterexample
    aggressiveToPair
    tt
    pairOrbitExact
    "reopen only the missing orbit/lift structure until the declared exact kernel consumer is restored"

repairRestoresPairEligibility :
  MDL.Eligible exactKernelCompressionProblem pairOrbitQuotientStage
repairRestoresPairEligibility = MDL.repairProvidesEligibleRefinement aggressiveLocalRepair

------------------------------------------------------------------------
-- N-dimensional cost fabric.  Width is not the only cost coordinate.
------------------------------------------------------------------------

data RSACompressionCostAxis : Set where
  coordinateWidthAxis : RSACompressionCostAxis
  activeOrbitAxis : RSACompressionCostAxis
  replayWorkAxis : RSACompressionCostAxis
  proofDebtAxis : RSACompressionCostAxis

compressionCost : RSACompressionCostAxis → RSACompressionStage → Nat
compressionCost coordinateWidthAxis fullWidthStage = 256
compressionCost coordinateWidthAxis pairOrbitQuotientStage = 128
compressionCost coordinateWidthAxis aggressiveUncertifiedStage = 64
compressionCost activeOrbitAxis fullWidthStage = 256
compressionCost activeOrbitAxis pairOrbitQuotientStage = 128
compressionCost activeOrbitAxis aggressiveUncertifiedStage = 64
compressionCost replayWorkAxis fullWidthStage = 256
compressionCost replayWorkAxis pairOrbitQuotientStage = 128
compressionCost replayWorkAxis aggressiveUncertifiedStage = 64
compressionCost proofDebtAxis fullWidthStage = 0
compressionCost proofDebtAxis pairOrbitQuotientStage = 0
compressionCost proofDebtAxis aggressiveUncertifiedStage = 1

compressionAxisReference : RSACompressionCostAxis → String
compressionAxisReference coordinateWidthAxis = "carrier coordinate width"
compressionAxisReference activeOrbitAxis = "active retained orbit/fibre count proxy"
compressionAxisReference replayWorkAxis = "relative synthetic replay-work proxy"
compressionAxisReference proofDebtAxis = "unpaid exact consumer-proof debt"

rsaCompressionCostHyperfabric : MDL.CostHyperfabric exactKernelCompressionProblem
rsaCompressionCostHyperfabric =
  MDL.costHyperfabric RSACompressionCostAxis compressionCost compressionAxisReference

------------------------------------------------------------------------
-- Existing executed bidi receipt is the semantic donor for pair adequacy.
------------------------------------------------------------------------

pairExecutionReceipt : Bidi.PairOrbitQuotientExecutionReceipt
pairExecutionReceipt = Bidi.rsa260PairOrbitBidiReceipt

record CompressionExecutionWeld : Set where
  constructor compression-execution-weld
  field
    fullWidth : Nat
    quotientWidth : Nat
    quotientOperatorIntertwinesWithLift : Bool
    quotientKernelRecovered : Bool
    liftedKernelVerifiedUpstairs : Bool
    measuredReductionPaid : Bool
    productionRSA260MatrixUsed : Bool
open CompressionExecutionWeld public

currentCompressionExecutionWeld : CompressionExecutionWeld
currentCompressionExecutionWeld = compression-execution-weld
  (Bidi.PairOrbitQuotientExecutionReceipt.fullWidth pairExecutionReceipt)
  (Bidi.PairOrbitQuotientExecutionReceipt.quotientWidth pairExecutionReceipt)
  (Bidi.PairOrbitQuotientExecutionReceipt.quotientOperatorIntertwinesWithLift pairExecutionReceipt)
  (Bidi.PairOrbitQuotientExecutionReceipt.nonzeroQuotientKernelRecovered pairExecutionReceipt)
  (Bidi.PairOrbitQuotientExecutionReceipt.liftedKernelVerifiedUpstairs pairExecutionReceipt)
  true
  (Bidi.PairOrbitQuotientExecutionReceipt.productionRSA260MatrixUsed pairExecutionReceipt)

------------------------------------------------------------------------
-- Production artifact depth is also consumer-relative, but entry depth is not
-- information equivalence and does not erase dependencies on earlier carriers.
------------------------------------------------------------------------

data ProductionConsumer : Set where
  reconstructFullLinearAlgebra : ProductionConsumer
  enterAtKrylovState : ProductionConsumer
  inspectLingenOutput : ProductionConsumer
  inspectMksolOutput : ProductionConsumer
  inspectGatherOutput : ProductionConsumer

minimumEntryDepth : ProductionConsumer → Substitute.LAAdmissionDepth
minimumEntryDepth reconstructFullLinearAlgebra = Substitute.matrixInputDepth
minimumEntryDepth enterAtKrylovState = Substitute.krylovStateDepth
minimumEntryDepth inspectLingenOutput = Substitute.lingenOutputDepth
minimumEntryDepth inspectMksolOutput = Substitute.mksolOutputDepth
minimumEntryDepth inspectGatherOutput = Substitute.gatherOutputDepth

record ProductionCompressionReading : Set where
  constructor production-compression-reading
  field
    minimumEntryDepthIsConsumerRelative : Bool
    laterArtifactMayPayDeeperEntryPoint : Bool
    laterArtifactReconstructsEarlierMatrix : Bool
    acquisitionOrderMayDifferFromPaymentOrder : Bool
open ProductionCompressionReading public

canonicalProductionCompressionReading : ProductionCompressionReading
canonicalProductionCompressionReading = production-compression-reading
  true true false true

substituteBoundary : Substitute.SubstituteAdmissionBoundary
substituteBoundary = Substitute.currentSubstituteAdmissionBoundary

------------------------------------------------------------------------
-- Exact-vs-approximate boundary.
--
-- Approximate consumer margins are repo-native and useful elsewhere, but the
-- exact GF(2) kernel consumer here currently has no declared approximation
-- margin.  Approximation may be introduced only for a separately declared
-- consumer whose decision is proved stable under that error.
------------------------------------------------------------------------

record RSAApproximationBoundary : Set where
  constructor rsa-approximation-boundary
  field
    approximateCompressionFrameworkExists : Bool
    exactGF2KernelConsumerCurrentlyUsesApproximateMargin : Bool
    approximatePerformanceTelemetryMayBeSeparateConsumer : Bool
    approximateDecisionSafetyImpliesExactKernelIdentity : Bool
open RSAApproximationBoundary public

canonicalRSAApproximationBoundary : RSAApproximationBoundary
canonicalRSAApproximationBoundary = rsa-approximation-boundary
  true false true false

minimalFidelityBoundary : Minimal.MinimalFidelityBoundary
minimalFidelityBoundary = Minimal.canonicalMinimalFidelityBoundary

approximateFidelityBoundary : Approx.ConsumerApproximateFidelityBoundary
approximateFidelityBoundary = Approx.canonicalConsumerApproximateFidelityBoundary

reductionSearchBoundary : Search.ReductionSearchBoundary
reductionSearchBoundary = Search.canonicalReductionSearchBoundary

------------------------------------------------------------------------
-- Roadmap consequence.
------------------------------------------------------------------------

record RSACompressionRoadmapBoundary : Set where
  constructor rsa-compression-roadmap-boundary
  field
    consumerAdequacyBeforeCostRanking : Bool
    pairOrbitCompressionAdequateOnSyntheticConsumer : Bool
    smallerUncertifiedCandidateMayWinRawWidth : Bool
    smallerUncertifiedCandidateMayEnterEligibleStratum : Bool
    counterexampleMayDriveLocalFibreRepair : Bool
    multiAxisCostsRemainNonScalarized : Bool
    productionArtifactDepthIsConsumerRelative : Bool
    compressionMayReplaceSameObjectAcquisition : Bool
    productionCompressionSearchPaid : Bool
open RSACompressionRoadmapBoundary public

currentRSACompressionRoadmapBoundary : RSACompressionRoadmapBoundary
currentRSACompressionRoadmapBoundary = rsa-compression-roadmap-boundary
  true true true false true true true false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SmallestCarrierImpliesAdequate : Set where
data LargestSymmetryImpliesBestCompression : Set where
data ApproximateTelemetrySafetyImpliesExactKernel : Set where
data CompressionImpliesProductionArtifactCustody : Set where

smallestCarrierDoesNotCreateAdequacy : SmallestCarrierImpliesAdequate → ⊥
smallestCarrierDoesNotCreateAdequacy ()

largestSymmetryDoesNotCreateBestCompression : LargestSymmetryImpliesBestCompression → ⊥
largestSymmetryDoesNotCreateBestCompression ()

approximateTelemetryDoesNotCreateExactKernel : ApproximateTelemetrySafetyImpliesExactKernel → ⊥
approximateTelemetryDoesNotCreateExactKernel ()

compressionDoesNotCreateArtifactCustody : CompressionImpliesProductionArtifactCustody → ⊥
compressionDoesNotCreateArtifactCustody ()
