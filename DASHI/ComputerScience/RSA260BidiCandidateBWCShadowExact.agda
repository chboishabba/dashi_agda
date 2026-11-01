module DASHI.ComputerScience.RSA260BidiCandidateBWCShadowExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.RobustExperimentInferenceFrontierExact as Experiment
import DASHI.ComputerScience.RSA260BidiCandidateExperimentExact as Candidate
import DASHI.ComputerScience.RSA260LACarrierBidiDerivationExact as BidiCarrier

------------------------------------------------------------------------
-- PREPARED BWC-SHAPED SHADOW EXPERIMENT
--
-- A : 924 x 512 repaired GF(2) shadow.
-- B = A A^T : 924 x 924 square experimental left-nullspace preparation.
--
-- This pays an executable consumer for the candidate CONSTRUCTION, not the
-- historical CADO prepared encoding.  In particular B = A A^T is an explicit
-- experimental adapter and is not promoted to production-prep identity.
------------------------------------------------------------------------

candidateExperiment : Candidate.CandidateExperimentExecutionReceipt
candidateExperiment = Candidate.currentCandidateExperimentExecutionReceipt

bidiCarrierBoundary : BidiCarrier.BidiCarrierDerivationBoundary
bidiCarrierBoundary = BidiCarrier.canonicalBidiCarrierDerivationBoundary

experimentBoundary : Experiment.RobustExperimentFrontierBoundary
experimentBoundary = Experiment.canonicalRobustExperimentFrontierBoundary

record BWCShadowRuntimeSource : Set where
  constructor bwc-shadow-runtime-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    sourceEquivalentExecutionPassed : Bool
    exactGitBlobExecuted : Bool
open BWCShadowRuntimeSource public

currentBWCShadowRuntimeSource : BWCShadowRuntimeSource
currentBWCShadowRuntimeSource = bwc-shadow-runtime-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_bidi_candidate_bwc_shadow_oracle.c"
  "d6f12710c94bf1ba9755b12b89e7a6af9531b0de"
  "5b0a57672e074b0471c6868c836e580bc5ffc5f5"
  true
  true

record BWCShadowExecutionReceipt : Set where
  constructor bwc-shadow-execution-receipt
  field
    rectangularRows : Nat
    rectangularColumns : Nat
    rectangularRank : Nat
    rectangularLeftNullity : Nat
    preparedRows : Nat
    preparedColumns : Nat
    preparedRank : Nat
    preparedNullity : Nat
    recoveredKernelSatisfiesATZero : Bool
    recoveredKernelSatisfiesPreparedZero : Bool
    explicitPreparedEqualsFactorizedApplication : Bool
    krylovSteps : Nat
    packedScalarFactorizedKrylovAgree : Bool
    krylovDigest : String
    projectionWidth : Nat
    projectionTerms : Nat
    projectionDigest : String
    productionPreparedEncodingIdentityPaid : Bool
    productionBlockWiedemannReplayPaid : Bool
open BWCShadowExecutionReceipt public

currentBWCShadowExecutionReceipt : BWCShadowExecutionReceipt
currentBWCShadowExecutionReceipt = bwc-shadow-execution-receipt
  924 512 512 412
  924 924 512 412
  true true true
  64 true "9dd84ecd118d65f2"
  8 32 "40645b5430eb1636"
  false false

record PreparedShadowConsumerBoundary : Set where
  constructor prepared-shadow-consumer-boundary
  field
    leftNullspaceConsumerPreservedOnShadow : Bool
    preparedAndRectangularNullitiesMatch : Bool
    packedSpMVConsumerPaidOnShadow : Bool
    scalarCrossCheckPaidOnShadow : Bool
    factorizedCrossCheckPaidOnShadow : Bool
    krylovConsumerPaidOnShadow : Bool
    projectionSequenceConsumerPaidOnShadow : Bool
    exactProductionWidth256ProjectionPaid : Bool
    productionCheckpointCadencePaidByThisExperiment : Bool
    productionGeneratorLengthPaidByThisExperiment : Bool
    productionPreparedEncodingPaid : Bool
open PreparedShadowConsumerBoundary public

canonicalPreparedShadowConsumerBoundary : PreparedShadowConsumerBoundary
canonicalPreparedShadowConsumerBoundary = prepared-shadow-consumer-boundary
  true true true true true true true
  false false false false

------------------------------------------------------------------------
-- Experiment escalation.
------------------------------------------------------------------------

data PreparedShadowResidual : Set where
  raiseShadowProjectionWidthToward256 : PreparedShadowResidual
  runMatrixGeneratorConsumerOnCandidateShadow : PreparedShadowResidual
  runKernelRecoveryThroughGeneratorConsumer : PreparedShadowResidual
  compareAlternativePreparationAdapters : PreparedShadowResidual
  validateAgainstSameObjectProductionArtifact : PreparedShadowResidual

firstPreparedShadowResidual : PreparedShadowResidual
firstPreparedShadowResidual = raiseShadowProjectionWidthToward256

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data AATShadowImpliesCADOProductionPrep : Set where
data MatchingShadowNullityImpliesProductionNullity : Set where
data ShadowKrylovImpliesProductionKrylov : Set where
data ProjectionDigestImpliesGeneratorCompatibility : Set where

aatShadowDoesNotIdentifyCADOProductionPrep : AATShadowImpliesCADOProductionPrep → ⊥
aatShadowDoesNotIdentifyCADOProductionPrep ()

shadowNullityDoesNotCreateProductionNullity : MatchingShadowNullityImpliesProductionNullity → ⊥
shadowNullityDoesNotCreateProductionNullity ()

shadowKrylovDoesNotCreateProductionKrylov : ShadowKrylovImpliesProductionKrylov → ⊥
shadowKrylovDoesNotCreateProductionKrylov ()

projectionDigestDoesNotCreateGeneratorCompatibility : ProjectionDigestImpliesGeneratorCompatibility → ⊥
projectionDigestDoesNotCreateGeneratorCompatibility ()
