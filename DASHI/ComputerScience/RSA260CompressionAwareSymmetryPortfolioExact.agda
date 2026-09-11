module DASHI.ComputerScience.RSA260CompressionAwareSymmetryPortfolioExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.ComputerScience.RSA260ConsumerRelativeCompressionCrossPollinationExact as Compression
import DASHI.ComputerScience.RSA260C3OrbitReducerHyperfabricExact as C3
import DASHI.ComputerScience.RSA260MixedActionNDimFibreInferenceExact as Mixed
import DASHI.ComputerScience.RSA260FullReInferenceSymmetryNullExact as Nulls

------------------------------------------------------------------------
-- COMPRESSION-AWARE SYMMETRY PORTFOLIO
--
-- Candidate actions/quotients remain separate until exact consumer adequacy is
-- paid.  Width or symmetry size may generate candidates, but only the eligible
-- stratum is cost-ranked.  Counterexamples reopen the missing certificate
-- fibre rather than globally discarding the richer carrier.
------------------------------------------------------------------------

data PortfolioCandidate : Set where
  full256Candidate : PortfolioCandidate
  pair128Candidate : PortfolioCandidate
  c3x88Candidate : PortfolioCandidate
  v4x76Candidate : PortfolioCandidate
  aggressive64Candidate : PortfolioCandidate

candidateReference : PortfolioCandidate → String
candidateReference full256Candidate = "full 256-coordinate synthetic carrier"
candidateReference pair128Candidate = "128-coordinate pair-orbit quotient with quotient/lift kernel receipt"
candidateReference c3x88Candidate = "88-coordinate all-C3-orbit exact-kernel quotient"
candidateReference v4x76Candidate = "76-coordinate all-V4-orbit exact-kernel quotient"
candidateReference aggressive64Candidate = "64-coordinate illustrative aggressive quotient candidate"

candidateWidth : PortfolioCandidate → Nat
candidateWidth full256Candidate = 256
candidateWidth pair128Candidate = 128
candidateWidth c3x88Candidate = 88
candidateWidth v4x76Candidate = 76
candidateWidth aggressive64Candidate = 64

------------------------------------------------------------------------
-- Exact-kernel consumer eligibility.
------------------------------------------------------------------------

data ExactKernelPortfolioAdequacy : PortfolioCandidate → Set where
  full256Exact : ExactKernelPortfolioAdequacy full256Candidate
  pair128Exact : ExactKernelPortfolioAdequacy pair128Candidate
  c3x88Exact : ExactKernelPortfolioAdequacy c3x88Candidate
  v4x76Exact : ExactKernelPortfolioAdequacy v4x76Candidate

candidateAdmissible : PortfolioCandidate → Set
candidateAdmissible candidate = ⊤

candidateExactKernelAdequate : PortfolioCandidate → Set
candidateExactKernelAdequate = ExactKernelPortfolioAdequacy

data PortfolioRefines : PortfolioCandidate → PortfolioCandidate → Set where
  fullReflexive : PortfolioRefines full256Candidate full256Candidate
  pairReflexive : PortfolioRefines pair128Candidate pair128Candidate
  c3Reflexive : PortfolioRefines c3x88Candidate c3x88Candidate
  v4Reflexive : PortfolioRefines v4x76Candidate v4x76Candidate
  aggressiveReflexive : PortfolioRefines aggressive64Candidate aggressive64Candidate
  aggressiveToPair : PortfolioRefines aggressive64Candidate pair128Candidate
  pairToFull : PortfolioRefines pair128Candidate full256Candidate

portfolioProblem : MDL.ConsumerMDLProblem
portfolioProblem =
  MDL.consumerMDLProblem
    PortfolioCandidate
    candidateAdmissible
    candidateExactKernelAdequate
    candidateWidth
    PortfolioRefines
    candidateReference
    "coordinate width used only as one ranking coordinate after exact-kernel consumer eligibility"
    "synthetic exact GF(2) quotient/lift kernel consumer"

full256Eligible : MDL.Eligible portfolioProblem full256Candidate
full256Eligible = tt , full256Exact

pair128Eligible : MDL.Eligible portfolioProblem pair128Candidate
pair128Eligible = tt , pair128Exact

c3x88Eligible : MDL.Eligible portfolioProblem c3x88Candidate
c3x88Eligible = tt , c3x88Exact

v4x76Eligible : MDL.Eligible portfolioProblem v4x76Candidate
v4x76Eligible = tt , v4x76Exact

aggressiveAdequacyUnpaid : ExactKernelPortfolioAdequacy aggressive64Candidate → ⊥
aggressiveAdequacyUnpaid ()

------------------------------------------------------------------------
-- Candidate-specific reopen fibre for the remaining cheapest raw candidate.
------------------------------------------------------------------------

data MissingCertificateFibre : PortfolioCandidate → Set where
  aggressiveNeedsActionAndLift : MissingCertificateFibre aggressive64Candidate

record CandidateRepairResidual (candidate : PortfolioCandidate) : Set where
  constructor candidate-repair-residual
  field
    Missing : Set
    missing : Missing
    residualReference : String
open CandidateRepairResidual public

aggressiveRepairResidual : CandidateRepairResidual aggressive64Candidate
aggressiveRepairResidual = candidate-repair-residual
  (MissingCertificateFibre aggressive64Candidate)
  aggressiveNeedsActionAndLift
  "reopen action validity and exact quotient/lift/kernel structure before allowing the smallest raw-width candidate into the eligible stratum"

------------------------------------------------------------------------
-- Multi-axis portfolio costs.  These are declared ranking coordinates, not a
-- scalar scientific score.
------------------------------------------------------------------------

data PortfolioCostAxis : Set where
  widthAxis : PortfolioCostAxis
  activeCarrierAxis : PortfolioCostAxis
  replayWorkAxis : PortfolioCostAxis
  exactConsumerProofDebtAxis : PortfolioCostAxis

portfolioCost : PortfolioCostAxis → PortfolioCandidate → Nat
portfolioCost widthAxis full256Candidate = 256
portfolioCost widthAxis pair128Candidate = 128
portfolioCost widthAxis c3x88Candidate = 88
portfolioCost widthAxis v4x76Candidate = 76
portfolioCost widthAxis aggressive64Candidate = 64
portfolioCost activeCarrierAxis candidate = candidateWidth candidate
portfolioCost replayWorkAxis candidate = candidateWidth candidate
portfolioCost exactConsumerProofDebtAxis full256Candidate = 0
portfolioCost exactConsumerProofDebtAxis pair128Candidate = 0
portfolioCost exactConsumerProofDebtAxis c3x88Candidate = 0
portfolioCost exactConsumerProofDebtAxis v4x76Candidate = 0
portfolioCost exactConsumerProofDebtAxis aggressive64Candidate = 2

portfolioAxisReference : PortfolioCostAxis → String
portfolioAxisReference widthAxis = "quotient/full carrier coordinate width"
portfolioAxisReference activeCarrierAxis = "active retained coordinate/orbit proxy"
portfolioAxisReference replayWorkAxis = "relative synthetic replay-work proxy"
portfolioAxisReference exactConsumerProofDebtAxis = "missing exact quotient/lift/kernel consumer certificate count proxy"

portfolioCostHyperfabric : MDL.CostHyperfabric portfolioProblem
portfolioCostHyperfabric = MDL.costHyperfabric PortfolioCostAxis portfolioCost portfolioAxisReference

------------------------------------------------------------------------
-- Existing evidence donors remain typed and non-promoting.
------------------------------------------------------------------------

c3Execution : C3.C3OrbitReducerExecutionReceipt
c3Execution = C3.currentC3OrbitReducerExecutionReceipt

v4Execution : Mixed.MultiFibreV4Receipt
v4Execution = Mixed.currentMultiFibreV4Receipt

nullExecution : Nulls.FullReInferenceNullReceipt
nullExecution = Nulls.currentFullReInferenceNullReceipt

record KernelCertificationOracleSource : Set where
  constructor kernel-certification-oracle-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    compiler : String
    exactGitBlobExecuted : Bool
open KernelCertificationOracleSource public

currentKernelCertificationOracleSource : KernelCertificationOracleSource
currentKernelCertificationOracleSource = kernel-certification-oracle-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_compression_portfolio_kernel_cert_oracle.c"
  "acb49112794b7220089cf6a507690e45ede87a76"
  "72a7a951cb0d0921dd38ab7dcd7586ca17f5d846"
  "gcc -std=c11 -O3 -Wall -Wextra -pedantic"
  true

record KernelCertificationExecutionReceipt : Set where
  constructor kernel-certification-execution-receipt
  field
    c3FullWidth : Nat
    c3QuotientWidth : Nat
    c3FullRank : Nat
    c3FullNullity : Nat
    c3QuotientRank : Nat
    c3QuotientNullity : Nat
    c3IntertwiningChecks : Nat
    c3LiftedKernelWeight : Nat
    v4FullWidth : Nat
    v4QuotientWidth : Nat
    v4FullRank : Nat
    v4FullNullity : Nat
    v4QuotientRank : Nat
    v4QuotientNullity : Nat
    v4IntertwiningChecks : Nat
    v4LiftedKernelWeight : Nat
    nullityPreservedForBoth : Bool
    liftedKernelVerifiedForBoth : Bool
    productionRSA260MatrixUsed : Bool
open KernelCertificationExecutionReceipt public

currentKernelCertificationExecutionReceipt : KernelCertificationExecutionReceipt
currentKernelCertificationExecutionReceipt = kernel-certification-execution-receipt
  256 88 252 4 84 4 22528 1
  256 76 255 1 75 1 19456 1
  true true false

record PortfolioEvidenceBoundary : Set where
  constructor portfolio-evidence-boundary
  field
    pairExactKernelAdequacyPaid : Bool
    c3ActionAndClosureEvidencePaid : Bool
    c3ExactKernelAdequacyPaid : Bool
    v4ActionAndNullEvidencePaid : Bool
    v4ExactKernelAdequacyPaid : Bool
    smallestRawWidthCandidateEligible : Bool
    exactCertificationBlobExecuted : Bool
    nullEvidenceMayReplaceExactKernelCertificate : Bool
open PortfolioEvidenceBoundary public

canonicalPortfolioEvidenceBoundary : PortfolioEvidenceBoundary
canonicalPortfolioEvidenceBoundary = portfolio-evidence-boundary
  true true true true true false true false

------------------------------------------------------------------------
-- Compression-aware search policy.
------------------------------------------------------------------------

record CompressionAwareSearchPolicy : Set where
  constructor compression-aware-search-policy
  field
    generateCandidateActionsBeforeRanking : Bool
    requireConsumerCertificateBeforeCostRanking : Bool
    preserveUncertifiedCandidatesAsReopenable : Bool
    counterexampleReopensOnlyMissingFibre : Bool
    largestSymmetryAutomaticallyWins : Bool
    smallestWidthAutomaticallyWins : Bool
    paretoAxesRemainApplicationDeclared : Bool
    fullWidthFallbackAlwaysRetained : Bool
    oldConsumerConflictGraphMayBeReusedWithoutRetesting : Bool
open CompressionAwareSearchPolicy public

canonicalCompressionAwareSearchPolicy : CompressionAwareSearchPolicy
canonicalCompressionAwareSearchPolicy = compression-aware-search-policy
  true true true true false false true true false

reductionSearchBoundary : Search.ReductionSearchBoundary
reductionSearchBoundary = Search.canonicalReductionSearchBoundary

compressionBoundary : Compression.RSACompressionRoadmapBoundary
compressionBoundary = Compression.currentRSACompressionRoadmapBoundary

------------------------------------------------------------------------
-- Current finite-portfolio reading.
------------------------------------------------------------------------

record CurrentPortfolioSelectionBoundary : Set where
  constructor current-portfolio-selection-boundary
  field
    eligibleCandidateCount : Nat
    cheapestEligibleWidth : Nat
    cheapestEligibleCandidateIsV4x76 : Bool
    aggressive64IsCheaperRawButIneligible : Bool
    selectedCandidateClaimIsSyntheticOnly : Bool
    productionOptimalityPaid : Bool
open CurrentPortfolioSelectionBoundary public

currentPortfolioSelectionBoundary : CurrentPortfolioSelectionBoundary
currentPortfolioSelectionBoundary = current-portfolio-selection-boundary
  4 76 true true true false

------------------------------------------------------------------------
-- Next residual: replace width/work proxies with measured replay, memory, and
-- communication costs before claiming a richer production Pareto frontier.
------------------------------------------------------------------------

data CompressionPortfolioResidual : Set where
  addMeasuredReplayMemoryCommunicationCosts : CompressionPortfolioResidual
  computeSyntheticMeasuredParetoFrontier : CompressionPortfolioResidual
  computeProductionEligibleParetoFrontier : CompressionPortfolioResidual
  runProductionCompressionPortfolio : CompressionPortfolioResidual

firstCompressionPortfolioResidual : CompressionPortfolioResidual
firstCompressionPortfolioResidual = addMeasuredReplayMemoryCommunicationCosts

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data StructuralSymmetryImpliesKernelAdequacy : Set where
data BetterNullPImpliesExactConsumerAdequacy : Set where
data PriorConsumerConflictImpliesCurrentConsumerConflict : Set where
data ParetoCostImpliesMathematicalTruth : Set where
data CheapestCandidateImpliesSelectedWithoutEligibility : Set where

actionDoesNotCreateKernelAdequacy : StructuralSymmetryImpliesKernelAdequacy → ⊥
actionDoesNotCreateKernelAdequacy ()

nullEvidenceDoesNotCreateKernelAdequacy : BetterNullPImpliesExactConsumerAdequacy → ⊥
nullEvidenceDoesNotCreateKernelAdequacy ()

priorConsumerConflictDoesNotTransferAutomatically : PriorConsumerConflictImpliesCurrentConsumerConflict → ⊥
priorConsumerConflictDoesNotTransferAutomatically ()

paretoCostDoesNotCreateTruth : ParetoCostImpliesMathematicalTruth → ⊥
paretoCostDoesNotCreateTruth ()

cheapestRawDoesNotCreateSelection : CheapestCandidateImpliesSelectedWithoutEligibility → ⊥
cheapestRawDoesNotCreateSelection ()
