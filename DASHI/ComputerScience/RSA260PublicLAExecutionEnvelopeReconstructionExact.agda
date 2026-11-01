module DASHI.ComputerScience.RSA260PublicLAExecutionEnvelopeReconstructionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact as Diligence

------------------------------------------------------------------------
-- PUBLIC RSA-260 LINEAR-ALGEBRA EXECUTION ENVELOPE
--
-- Reconstructs only coordinates explicitly reported by Eric Lu's Cognition
-- primary technical account.  It does not manufacture matrix/checkpoint bytes.
------------------------------------------------------------------------

primarySource : Source.AttributedSource
primarySource =
  Source.mkWebSource
    "Eric Lu"
    "Factoring RSA-260"
    "Cognition"
    "2026-09-09"
    "https://cognition.com/blog/factoring-rsa-260"
    Source.publicAttribution

record PublicLAEnvelopeSourceCoordinates : Set where
  constructor public-la-envelope-source-coordinates
  field
    source : Source.AttributedSource
    doi : Diligence.IdentifierApplicability
    qid : Diligence.IdentifierApplicability
    oeis : Diligence.IdentifierApplicability
    sourceIdentityCreatesArtifactCustody : Bool
open PublicLAEnvelopeSourceCoordinates public

currentPublicLAEnvelopeSourceCoordinates : PublicLAEnvelopeSourceCoordinates
currentPublicLAEnvelopeSourceCoordinates = public-la-envelope-source-coordinates
  primarySource
  Diligence.identifierNotApplicable
  Diligence.identifierUnresolved
  Diligence.identifierNotApplicable
  false

record PublicLAExecutionEnvelope : Set where
  constructor public-la-execution-envelope
  field
    matrixRows : Nat
    matrixColumns : Nat
    matrixNonzeros : Nat
    krylovSequences : Nat
    krylovWidth : Nat
    blockM : Nat
    blockN : Nat
    finalIterationsPerSequence : Nat
    checkpointStride : Nat
    checkpointIntervalsPerSequence : Nat
    retainedCheckpointStride : Nat
    completeRetainedStrideMultiples : Nat
    terminalRemainderAfterRetainedStride : Nat
    lingenGeneratorLength : Nat
    mksolPartialSolutionFiles : Nat
    gatheredKernelVectors : Nat
    nonzeroDependencies : Nat
    firstFactorDependency : Nat
open PublicLAExecutionEnvelope public

currentPublicLAExecutionEnvelope : PublicLAExecutionEnvelope
currentPublicLAExecutionEnvelope = public-la-execution-envelope
  656182601
  656182189
  98431741898
  2
  256
  512
  512
  2564096
  8192
  313
  32768
  78
  8192
  1281607
  40
  64
  26
  12

record PublicLAReconstructionBoundary : Set where
  constructor public-la-reconstruction-boundary
  field
    primaryExecutionEnvelopeReconstructed : Bool
    checkpointIndexLatticeReconstructed : Bool
    retainedCadenceReconstructed : Bool
    finalEndpointRetentionStatusResolved : Bool
    allocationHoverMetadataRecovered : Bool
    productionMatrixBytesAcquired : Bool
    productionCheckpointBytesAcquired : Bool
    productionGeneratorBytesAcquired : Bool
    productionKernelVectorBytesAcquired : Bool
    sameObjectP0Paid : Bool
open PublicLAReconstructionBoundary public

currentPublicLAReconstructionBoundary : PublicLAReconstructionBoundary
currentPublicLAReconstructionBoundary = public-la-reconstruction-boundary
  true true true false false false false false false false

record RuntimeManifestSource : Set where
  constructor runtime-manifest-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
    exactGitBlobExecuted : Bool
open RuntimeManifestSource public

currentRuntimeManifestSource : RuntimeManifestSource
currentRuntimeManifestSource = runtime-manifest-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_public_la_execution_envelope_manifest.c"
  "4ca05f4fd4bcd65ef3039570df53fd04842a92a5"
  "8734a6f299dd8f674918e5644f551618566048f7"
  false

------------------------------------------------------------------------
-- Snowball residuals.
------------------------------------------------------------------------

data LAArtifactResidual : Set where
  acquireFilteredOrPreparedMatrixBytes : LAArtifactResidual
  acquireKrylovCheckpointBytes : LAArtifactResidual
  acquireLingenGeneratorBytes : LAArtifactResidual
  acquireMksolPartialSolutionBytes : LAArtifactResidual
  acquireGatheredKernelVectorBytes : LAArtifactResidual
  recoverAllocationHoverMetadata : LAArtifactResidual

firstConclusionPayingLAArtifactResidual : LAArtifactResidual
firstConclusionPayingLAArtifactResidual = acquireFilteredOrPreparedMatrixBytes

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ExecutionEnvelopeImpliesArtifactBytes : Set where
data CheckpointCadenceImpliesCheckpointContents : Set where
data ChartPixelsImplyHoverMetadata : Set where
data PublicChallengeIntegerImpliesLAInput : Set where

envelopeDoesNotCreateArtifactBytes : ExecutionEnvelopeImpliesArtifactBytes → ⊥
envelopeDoesNotCreateArtifactBytes ()

cadenceDoesNotCreateCheckpointContents : CheckpointCadenceImpliesCheckpointContents → ⊥
cadenceDoesNotCreateCheckpointContents ()

chartPixelsDoNotCreateHoverMetadata : ChartPixelsImplyHoverMetadata → ⊥
chartPixelsDoNotCreateHoverMetadata ()

challengeIntegerDoesNotCreateLAInput : PublicChallengeIntegerImpliesLAInput → ⊥
challengeIntegerDoesNotCreateLAInput ()
