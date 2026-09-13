module DASHI.ComputerScience.RSA260ProductionArtifactSubstituteAdmissionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260PublicLAExecutionEnvelopeReconstructionExact as Envelope

------------------------------------------------------------------------
-- P0 SUBSTITUTE ADMISSION
--
-- A later-stage artifact may pay a deeper entry point into the production LA
-- pipeline without reconstructing earlier carriers.  Admission is therefore
-- typed by artifact class and deepest justified stage, not by filename.
------------------------------------------------------------------------

data ProductionArtifactClass : Set where
  executionMetadataOnly : ProductionArtifactClass
  matrixOrPreparedInput : ProductionArtifactClass
  krylovCheckpoint : ProductionArtifactClass
  lingenGenerator : ProductionArtifactClass
  completeMksolCollection : ProductionArtifactClass
  completeGatherKernelCollection : ProductionArtifactClass

data LAAdmissionDepth : Set where
  envelopeOnly : LAAdmissionDepth
  matrixInputDepth : LAAdmissionDepth
  krylovStateDepth : LAAdmissionDepth
  lingenOutputDepth : LAAdmissionDepth
  mksolOutputDepth : LAAdmissionDepth
  gatherOutputDepth : LAAdmissionDepth

record SameObjectIdentityGate : Set where
  constructor same-object-identity-gate
  field
    bytesAcquired : Bool
    digestBound : Bool
    primarySourceIdentityBound : Bool
    sameRunIdentityBound : Bool
open SameObjectIdentityGate public

record ArtifactConstraintProfile : Set where
  constructor artifact-constraint-profile
  field
    artifactClass : ProductionArtifactClass
    requiredDepth : LAAdmissionDepth
    mustMatchMatrixShape : Bool
    mustMatchCheckpointLattice : Bool
    mustMatchSequenceIdentity : Bool
    mustMatchGeneratorLength : Bool
    mustBindAllMksolFiles : Bool
    mustBindAllGatherVectors : Bool
    reconstructsFilteredMatrix : Bool
open ArtifactConstraintProfile public

matrixProfile : ArtifactConstraintProfile
matrixProfile = artifact-constraint-profile
  matrixOrPreparedInput matrixInputDepth
  true false false false false false true

checkpointProfile : ArtifactConstraintProfile
checkpointProfile = artifact-constraint-profile
  krylovCheckpoint krylovStateDepth
  false true true false false false false

generatorProfile : ArtifactConstraintProfile
generatorProfile = artifact-constraint-profile
  lingenGenerator lingenOutputDepth
  false false false true false false false

mksolProfile : ArtifactConstraintProfile
mksolProfile = artifact-constraint-profile
  completeMksolCollection mksolOutputDepth
  false false false false true false false

gatherProfile : ArtifactConstraintProfile
gatherProfile = artifact-constraint-profile
  completeGatherKernelCollection gatherOutputDepth
  false false false false false true false

record PublicAdmissionConstants : Set where
  constructor public-admission-constants
  field
    matrixRows : Nat
    matrixColumns : Nat
    matrixNonzeros : Nat
    krylovWidth : Nat
    checkpointStride : Nat
    retainedStride : Nat
    finalIteration : Nat
    generatorLength : Nat
    mksolFileCount : Nat
    gatherVectorCount : Nat
open PublicAdmissionConstants public

currentPublicAdmissionConstants : PublicAdmissionConstants
currentPublicAdmissionConstants = public-admission-constants
  656182601
  656182189
  98431741898
  256
  8192
  32768
  2564096
  1281607
  40
  64

envelopeBoundary : Envelope.PublicLAReconstructionBoundary
envelopeBoundary = Envelope.currentPublicLAReconstructionBoundary

record SubstituteAdmissionBoundary : Set where
  constructor substitute-admission-boundary
  field
    metadataAlonePaysSameObjectArtifact : Bool
    matrixCandidateRequiresShapeNnzAndIdentity : Bool
    checkpointCandidateRequires8192Lattice : Bool
    checkpointCandidateRequiresSequenceIdentity : Bool
    regularRetainedClaimRequires32768Lattice : Bool
    terminalEndpointRetentionAutomaticallyPaid : Bool
    generatorCandidateRequiresLength1281607 : Bool
    mksolCollectionRequiresAll40Files : Bool
    gatherCollectionRequiresAll64Vectors : Bool
    downstreamArtifactReconstructsEarlierMatrix : Bool
    laterArtifactMayPayLaterEntryDepth : Bool
    p0SubstituteAdmissionOracleImplemented : Bool
    oracleExactGitBlobExecuted : Bool
open SubstituteAdmissionBoundary public

currentSubstituteAdmissionBoundary : SubstituteAdmissionBoundary
currentSubstituteAdmissionBoundary = substitute-admission-boundary
  false true true true true false true true true false true true false

record RuntimeAdmissionOracleSource : Set where
  constructor runtime-admission-oracle-source
  field
    repository : String
    branch : String
    path : String
    commit : String
    gitBlob : String
open RuntimeAdmissionOracleSource public

currentRuntimeAdmissionOracleSource : RuntimeAdmissionOracleSource
currentRuntimeAdmissionOracleSource = runtime-admission-oracle-source
  "chboishabba/dashiRTX"
  "agent/triadic-u8-runtime-oracle"
  "rsa260_p0_substitute_admission_oracle.c"
  "9d98d3f16df3c45a9bc026445709fa9b86413fe1"
  "379e85e5c6af78fa5e583cf8570e985cfcb02396"

------------------------------------------------------------------------
-- Snowball order: acquisition may be out of order; promotion may not.
------------------------------------------------------------------------

data SubstituteResidual : Set where
  bindExactRuntimeOracleExecution : SubstituteResidual
  acquireAnySameObjectLAArtifactBytes : SubstituteResidual
  applyTypedAdmissionGate : SubstituteResidual
  replayFromAdmittedDepth : SubstituteResidual
  verifyUpstairsAgainstEarlierCarrierWhenAvailable : SubstituteResidual

firstSubstituteResidual : SubstituteResidual
firstSubstituteResidual = bindExactRuntimeOracleExecution

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data FilenameImpliesArtifactIdentity : Set where
data DownstreamArtifactImpliesMatrixBytes : Set where
data CheckpointTimestampImpliesCheckpointBytes : Set where
data TerminalEndpointImpliesRetainedCheckpoint : Set where
data CountMatchImpliesSameObject : Set where

filenameDoesNotCreateIdentity : FilenameImpliesArtifactIdentity → ⊥
filenameDoesNotCreateIdentity ()

downstreamArtifactDoesNotReconstructMatrix : DownstreamArtifactImpliesMatrixBytes → ⊥
downstreamArtifactDoesNotReconstructMatrix ()

timestampDoesNotCreateCheckpointBytes : CheckpointTimestampImpliesCheckpointBytes → ⊥
timestampDoesNotCreateCheckpointBytes ()

terminalEndpointDoesNotCreateRetention : TerminalEndpointImpliesRetainedCheckpoint → ⊥
terminalEndpointDoesNotCreateRetention ()

countMatchDoesNotCreateSameObject : CountMatchImpliesSameObject → ⊥
countMatchDoesNotCreateSameObject ()
