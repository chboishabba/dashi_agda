module DASHI.ComputerScience.RSA260BidiCandidateExperimentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.RobustExperimentInferenceFrontierExact as Experiment
import DASHI.Core.ConsumerRelativeReductionSearchExact as ReductionSearch
import DASHI.ComputerScience.RSA260LACarrierBidiDerivationExact as BidiCarrier

------------------------------------------------------------------------
-- RUNNABLE BIDI CANDIDATE EXPERIMENT
--
-- Once bidi has produced a carrier CONSTRAINT FIBRE, uniqueness is not needed
-- in order to construct a runnable member and test declared consumers.
--
-- This owner therefore separates:
--   1. membership in the public production-shaped carrier contract,
--   2. held-out structural tests on the implicit full-sized candidate,
--   3. executable GF(2) rank/left-kernel tests on a smaller shadow,
--   4. historical same-object identity and full production BWC replay.
--
-- Passing 1--3 supports only those declared consumers.  It does not identify
-- the historical Cognition matrix and does not pay production Block-Wiedemann.
------------------------------------------------------------------------

data CandidateExperiment : Set where
  productionCarrierContract : CandidateExperiment
  heldOutRowStructure : CandidateExperiment
  shadowLeftKernel : CandidateExperiment
  productionBlockWiedemannReplay : CandidateExperiment

experimentScore : CandidateExperiment → Bool
experimentScore productionCarrierContract = true
experimentScore heldOutRowStructure = true
experimentScore shadowLeftKernel = true
experimentScore productionBlockWiedemannReplay = false

candidateExperimentDesign : Experiment.ExperimentDesign CandidateExperiment Bool
candidateExperimentDesign = Experiment.experimentDesign
  experimentScore
  (λ a b → a ≡ b)
  Bool

experimentFrontierBoundary : Experiment.RobustExperimentFrontierBoundary
experimentFrontierBoundary = Experiment.canonicalRobustExperimentFrontierBoundary

reductionSearchBoundary : ReductionSearch.ReductionSearchBoundary
reductionSearchBoundary = ReductionSearch.canonicalReductionSearchBoundary

bidiCarrierBoundary : BidiCarrier.BidiCarrierDerivationBoundary
bidiCarrierBoundary = BidiCarrier.canonicalBidiCarrierDerivationBoundary

------------------------------------------------------------------------
-- Production-shaped implicit candidate.
------------------------------------------------------------------------

record ImplicitProductionCandidate : Set where
  constructor implicit-production-candidate
  field
    rows : Nat
    columns : Nat
    nonzeros : Nat
    highDegreeRows : Nat
    highDegree : Nat
    ordinaryDegree : Nat
    rowExcess : Nat
    fieldIsGF2 : Bool
    rowQueryableWithoutMaterialisingWholeMatrix : Bool
    exactHistoricalNonzeroPlacementClaimed : Bool
open ImplicitProductionCandidate public

currentImplicitProductionCandidate : ImplicitProductionCandidate
currentImplicitProductionCandidate = implicit-production-candidate
  656182601
  656182189
  98431741898
  4351748
  151
  150
  412
  true
  true
  false

------------------------------------------------------------------------
-- Experiment provenance: failed first shadow -> local fibre repair -> held-out
-- retest.  The failed specimen is retained as a counterexample, not rewritten.
------------------------------------------------------------------------

record ShadowRepairHistory : Set where
  constructor shadow-repair-history
  field
    firstShadowRows : Nat
    firstShadowColumns : Nat
    firstShadowRank : Nat
    firstShadowLeftNullity : Nat
    targetLeftNullity : Nat
    firstShadowPassedTarget : Bool
    repairChangedProductionCandidate : Bool
    repairChangedOnlyShadowRowBase : Bool
    repairedShadowRank : Nat
    repairedShadowLeftNullity : Nat
    repairedShadowPassedTarget : Bool
open ShadowRepairHistory public

currentShadowRepairHistory : ShadowRepairHistory
currentShadowRepairHistory = shadow-repair-history
  924 512
  433 491
  412
  false
  false
  true
  512 412
  true

------------------------------------------------------------------------
-- Exact execution receipt.
------------------------------------------------------------------------

record CandidateExperimentRuntimeSource : Set where
  constructor candidate-experiment-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    compiler : String
    exactGitBlobExecuted : Bool
open CandidateExperimentRuntimeSource public

currentCandidateExperimentRuntimeSource : CandidateExperimentRuntimeSource
currentCandidateExperimentRuntimeSource = candidate-experiment-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_candidate_experiment_oracle.c"
  "1936a00368c8896e203c49f5cbcfca21680760e9"
  "f52c1e5cb33746b1ffeba53323f711a34885fcdc"
  "gcc -std=c11 -O2 -Wall -Wextra -pedantic"
  true

record CandidateExperimentExecutionReceipt : Set where
  constructor candidate-experiment-execution-receipt
  field
    productionContractPassed : Bool
    trainingBoundaryRowsChecked : Nat
    heldOutRowsChecked : Nat
    heldOutDigest : Nat
    heldOutStructuralTestPassed : Bool
    shadowRows : Nat
    shadowColumns : Nat
    shadowRank : Nat
    shadowLeftNullity : Nat
    shadowNonzeroLeftRelationVerified : Bool
    historicalSameObjectIdentityPaid : Bool
    productionBlockWiedemannReplayPaid : Bool
open CandidateExperimentExecutionReceipt public

currentCandidateExperimentExecutionReceipt : CandidateExperimentExecutionReceipt
currentCandidateExperimentExecutionReceipt = candidate-experiment-execution-receipt
  true
  8
  1024
  15547053997721034415
  true
  924 512 512 412
  true
  false
  false

------------------------------------------------------------------------
-- Consumer-relative interpretation.
------------------------------------------------------------------------

record CandidateConsumerSupportBoundary : Set where
  constructor candidate-consumer-support-boundary
  field
    publicCarrierShapeConsumerPaid : Bool
    exactNNZConsumerPaid : Bool
    rowQueryConsumerPaid : Bool
    heldOutStructuralConsumerPaid : Bool
    executableShadowRankConsumerPaid : Bool
    executableShadowLeftKernelConsumerPaid : Bool
    productionPreparedBWCEncodingConsumerPaid : Bool
    productionKrylovSequenceConsumerPaid : Bool
    productionGeneratorConsumerPaid : Bool
    historicalSameObjectConsumerPaid : Bool
    passingDeclaredConsumersImpliesPassingEveryConsumer : Bool
open CandidateConsumerSupportBoundary public

canonicalCandidateConsumerSupportBoundary : CandidateConsumerSupportBoundary
canonicalCandidateConsumerSupportBoundary = candidate-consumer-support-boundary
  true true true true true true
  false false false false
  false

------------------------------------------------------------------------
-- Next experiment escalation.
------------------------------------------------------------------------

data CandidateExperimentResidual : Set where
  constructPreparedBWCShadowAdapter : CandidateExperimentResidual
  runPackedSpMVConsumerOnShadow : CandidateExperimentResidual
  runKrylovProjectionGeneratorConsumersOnShadow : CandidateExperimentResidual
  compareMultipleIndependentCarrierCandidates : CandidateExperimentResidual
  acquireProductionSameObjectBytesForExternalValidation : CandidateExperimentResidual

firstCandidateExperimentResidual : CandidateExperimentResidual
firstCandidateExperimentResidual = constructPreparedBWCShadowAdapter

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data RunnableCandidateImpliesHistoricalMatrix : Set where
data HeldOutRowsImpliesFullBWCReplay : Set where
data ShadowKernelImpliesProductionKernel : Set where
data ExperimentFitImpliesModelAdequacy : Set where

data PassingSomeConsumersImpliesUniversalAdequacy : Set where

runnableCandidateDoesNotCreateHistoricalIdentity : RunnableCandidateImpliesHistoricalMatrix → ⊥
runnableCandidateDoesNotCreateHistoricalIdentity ()

heldOutRowsDoNotCreateBWCReplay : HeldOutRowsImpliesFullBWCReplay → ⊥
heldOutRowsDoNotCreateBWCReplay ()

shadowKernelDoesNotCreateProductionKernel : ShadowKernelImpliesProductionKernel → ⊥
shadowKernelDoesNotCreateProductionKernel ()

experimentFitDoesNotCreateAdequacy : ExperimentFitImpliesModelAdequacy → ⊥
experimentFitDoesNotCreateAdequacy ()

someConsumersDoNotCreateUniversalAdequacy : PassingSomeConsumersImpliesUniversalAdequacy → ⊥
someConsumersDoNotCreateUniversalAdequacy ()
