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
  c3x172Candidate : PortfolioCandidate
  v4x76Candidate : PortfolioCandidate
  aggressive64Candidate : PortfolioCandidate

candidateReference : PortfolioCandidate → String
candidateReference full256Candidate = "full 256-coordinate synthetic carrier"
candidateReference pair128Candidate = "128-coordinate pair-orbit quotient with quotient/lift kernel receipt"
candidateReference c3x172Candidate = "172-coordinate C3 closed-batch quotient candidate"
candidateReference v4x76Candidate = "76-coordinate multifibre V4/null-supported quotient candidate"
candidateReference aggressive64Candidate = "64-coordinate illustrative aggressive quotient candidate"

candidateWidth : PortfolioCandidate → Nat
candidateWidth full256Candidate = 256
candidateWidth pair128Candidate = 128
candidateWidth c3x172Candidate = 172
candidateWidth v4x76Candidate = 76
candidateWidth aggressive64Candidate = 64

------------------------------------------------------------------------
-- Exact-kernel consumer eligibility.
--
-- Only full256 and pair128 currently carry the required exact-kernel adequacy
-- receipt.  C3/V4 results pay structural action/commutation/null information,
-- but do not yet carry the same quotient-kernel-lift certificate.
------------------------------------------------------------------------

data ExactKernelPortfolioAdequacy : PortfolioCandidate → Set where
  full256Exact : ExactKernelPortfolioAdequacy full256Candidate
  pair128Exact : ExactKernelPortfolioAdequacy pair128Candidate

candidateAdmissible : PortfolioCandidate → Set
candidateAdmissible candidate = ⊤

candidateExactKernelAdequate : PortfolioCandidate → Set
candidateExactKernelAdequate = ExactKernelPortfolioAdequacy

data PortfolioRefines : PortfolioCandidate → PortfolioCandidate → Set where
  fullReflexive : PortfolioRefines full256Candidate full256Candidate
  pairReflexive : PortfolioRefines pair128Candidate pair128Candidate
  c3Reflexive : PortfolioRefines c3x172Candidate c3x172Candidate
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

c3AdequacyUnpaid : ExactKernelPortfolioAdequacy c3x172Candidate → ⊥
c3AdequacyUnpaid ()

v4AdequacyUnpaid : ExactKernelPortfolioAdequacy v4x76Candidate → ⊥
v4AdequacyUnpaid ()

aggressiveAdequacyUnpaid : ExactKernelPortfolioAdequacy aggressive64Candidate → ⊥
aggressiveAdequacyUnpaid ()

------------------------------------------------------------------------
-- Candidate-specific reopen fibres.
------------------------------------------------------------------------

data MissingCertificateFibre : PortfolioCandidate → Set where
  c3NeedsExactQuotientLiftKernel : MissingCertificateFibre c3x172Candidate
  v4NeedsExactQuotientLiftKernel : MissingCertificateFibre v4x76Candidate
  aggressiveNeedsActionAndLift : MissingCertificateFibre aggressive64Candidate

record CandidateRepairResidual (candidate : PortfolioCandidate) : Set where
  constructor candidate-repair-residual
  field
    Missing : Set
    missing : Missing
    residualReference : String
open CandidateRepairResidual public

c3RepairResidual : CandidateRepairResidual c3x172Candidate
c3RepairResidual = candidate-repair-residual
  (MissingCertificateFibre c3x172Candidate)
  c3NeedsExactQuotientLiftKernel
  "retain C3 action/closure result; reopen only exact quotient operator, kernel recovery, and upstairs lift verification"

v4RepairResidual : CandidateRepairResidual v4x76Candidate
v4RepairResidual = candidate-repair-residual
  (MissingCertificateFibre v4x76Candidate)
  v4NeedsExactQuotientLiftKernel
  "retain multifibre V4 inference and null evidence; reopen only exact quotient/lift/kernel consumer certificate"

aggressiveRepairResidual : CandidateRepairResidual aggressive64Candidate
aggressiveRepairResidual = candidate-repair-residual
  (MissingCertificateFibre aggressive64Candidate)
  aggressiveNeedsActionAndLift
  "reopen action validity and lift structure before allowing the smallest raw-width candidate into the eligible stratum"

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
portfolioCost widthAxis c3x172Candidate = 172
portfolioCost widthAxis v4x76Candidate = 76
portfolioCost widthAxis aggressive64Candidate = 64
portfolioCost activeCarrierAxis candidate = candidateWidth candidate
portfolioCost replayWorkAxis candidate = candidateWidth candidate
portfolioCost exactConsumerProofDebtAxis full256Candidate = 0
portfolioCost exactConsumerProofDebtAxis pair128Candidate = 0
portfolioCost exactConsumerProofDebtAxis c3x172Candidate = 1
portfolioCost exactConsumerProofDebtAxis v4x76Candidate = 1
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

record PortfolioEvidenceBoundary : Set where
  constructor portfolio-evidence-boundary
  field
    pairExactKernelAdequacyPaid : Bool
    c3ActionAndClosureEvidencePaid : Bool
    c3ExactKernelAdequacyPaid : Bool
    v4ActionAndNullEvidencePaid : Bool
    v4ExactKernelAdequacyPaid : Bool
    smallestRawWidthCandidateEligible : Bool
    nullEvidenceMayReplaceExactKernelCertificate : Bool
open PortfolioEvidenceBoundary public

canonicalPortfolioEvidenceBoundary : PortfolioEvidenceBoundary
canonicalPortfolioEvidenceBoundary = portfolio-evidence-boundary
  true true false true false false false

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
open CompressionAwareSearchPolicy public

canonicalCompressionAwareSearchPolicy : CompressionAwareSearchPolicy
canonicalCompressionAwareSearchPolicy = compression-aware-search-policy
  true true true true false false true true

reductionSearchBoundary : Search.ReductionSearchBoundary
reductionSearchBoundary = Search.canonicalReductionSearchBoundary

compressionBoundary : Compression.RSACompressionRoadmapBoundary
compressionBoundary = Compression.currentRSACompressionRoadmapBoundary

------------------------------------------------------------------------
-- Next residual: certify richer quotient candidates rather than generate ever
-- smaller uncertified carriers.
------------------------------------------------------------------------

data CompressionPortfolioResidual : Set where
  certifyC3ExactQuotientLiftKernel : CompressionPortfolioResidual
  certifyV4ExactQuotientLiftKernel : CompressionPortfolioResidual
  addMeasuredReplayMemoryCommunicationCosts : CompressionPortfolioResidual
  computeProductionEligibleParetoFrontier : CompressionPortfolioResidual
  runProductionCompressionPortfolio : CompressionPortfolioResidual

firstCompressionPortfolioResidual : CompressionPortfolioResidual
firstCompressionPortfolioResidual = certifyC3ExactQuotientLiftKernel

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data StructuralSymmetryImpliesKernelAdequacy : Set where
data BetterNullPImpliesExactConsumerAdequacy : Set where
data ParetoCostImpliesMathematicalTruth : Set where
data CheapestCandidateImpliesSelected : Set where

actionDoesNotCreateKernelAdequacy : StructuralSymmetryImpliesKernelAdequacy → ⊥
actionDoesNotCreateKernelAdequacy ()

nullEvidenceDoesNotCreateKernelAdequacy : BetterNullPImpliesExactConsumerAdequacy → ⊥
nullEvidenceDoesNotCreateKernelAdequacy ()

paretoCostDoesNotCreateTruth : ParetoCostImpliesMathematicalTruth → ⊥
paretoCostDoesNotCreateTruth ()

cheapestDoesNotCreateSelection : CheapestCandidateImpliesSelected → ⊥
cheapestDoesNotCreateSelection ()
