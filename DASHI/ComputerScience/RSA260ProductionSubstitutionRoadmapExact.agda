module DASHI.ComputerScience.RSA260ProductionSubstitutionRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260KrylovKernelRecoveryExact as SyntheticLA
import DASHI.ComputerScience.RSA260GNFSRunParameterArtifactSnowballExact as RunArtifact
import DASHI.ComputerScience.RSA260ProductionArtifactSubstituteAdmissionExact as Substitute

------------------------------------------------------------------------
-- RSA-260 PRODUCTION-SUBSTITUTION ROADMAP
--
-- The synthetic CPU Block-Wiedemann-shaped ladder is end-to-end through a
-- nonzero v with Mv=0.  The next conclusion-paying boundary is substitution
-- of a same-object RSA-260 LA artifact, followed by replay/parity.
--
-- A downstream artifact may pay a later entry depth without reconstructing
-- earlier carriers.  Therefore matrix/prep, checkpoint, generator, mksol and
-- gather artifacts are admitted by typed constraints rather than filename.
------------------------------------------------------------------------

record ProductionLAObservation : Set where
  constructor production-la-observation
  field
    sourceReference : String
    matrixRows : Nat
    matrixColumns : Nat
    matrixNonzeros : Nat
    matrixDensityLabel : String
    krylovIterationsPerSequence : Nat
    reportedSequenceCount : Nat
    reportedSequenceWidth : Nat
    reportedSIMDWidth : Nat
    reportedGeneratorLength : Nat
    reportedMksolPartialFiles : Nat
    reportedGatherKernelVectors : Nat
    reportedNonzeroDependencies : Nat
    firstFactorDependency : Nat
    mmImplementation : String
    communicationImplementation : String
    sourcePaid : Bool
open ProductionLAObservation public

rsa260ProductionLAObservation : ProductionLAObservation
rsa260ProductionLAObservation = production-la-observation
  "Eric Lu, Factoring RSA-260, RSA-260 stage table and parameters, 2026-09-09"
  656182601
  656182189
  98431741898
  "150.0 nonzeros per row (reported density)"
  2564096
  2
  256
  256
  1281607
  40
  64
  26
  12
  "cuda"
  "nccl"
  true

------------------------------------------------------------------------
-- Acquisition/search state.
--
-- Public execution-envelope coordinates are known.  Same-object bytes remain
-- separately unpaid.  A search miss is not proof of artifact absence.
------------------------------------------------------------------------

record ProductionArtifactAcquisitionState : Set where
  constructor production-artifact-acquisition-state
  field
    matrixBytesLocated : Bool
    krylovCheckpointBytesLocated : Bool
    generatorBytesLocated : Bool
    mksolBytesLocated : Bool
    gatheredKernelVectorBytesLocated : Bool
    exactSourceRevisionLocated : Bool
    exactExecutableDigestLocated : Bool
    targetedPublicSearchPerformed : Bool
    searchMissProvesNonexistence : Bool
open ProductionArtifactAcquisitionState public

currentProductionArtifactAcquisitionState : ProductionArtifactAcquisitionState
currentProductionArtifactAcquisitionState = production-artifact-acquisition-state
  false false false false false false false true false

------------------------------------------------------------------------
-- Prior/admission boundaries retained rather than collapsed.
------------------------------------------------------------------------

syntheticLABoundary : SyntheticLA.RSA260KrylovKernelRecoveryRoadmapBoundary
syntheticLABoundary = SyntheticLA.currentRSA260KrylovKernelRecoveryRoadmapBoundary

runArtifactBoundary : RunArtifact.RSA260RunParameterArtifactBoundary
runArtifactBoundary = RunArtifact.canonicalRSA260RunParameterArtifactBoundary

substituteAdmissionBoundary : Substitute.SubstituteAdmissionBoundary
substituteAdmissionBoundary = Substitute.currentSubstituteAdmissionBoundary

------------------------------------------------------------------------
-- Ordered residual router.
------------------------------------------------------------------------

data ProductionResidual : Set where
  acquireProductionMatrixOrEquivalentLAInput : ProductionResidual
  acquireProductionProjectionCheckpointOrGenerator : ProductionResidual
  bindExactModifiedSourceRevision : ProductionResidual
  reproduceProductionCPUReference : ProductionResidual
  reproduceCUDAKernel : ProductionResidual
  reproduceNCCLDistribution : ProductionResidual
  reproduceFullRSA260LinearAlgebra : ProductionResidual

firstUnpaidProductionResidual : ProductionResidual
firstUnpaidProductionResidual = acquireProductionMatrixOrEquivalentLAInput

record RSA260ProductionSubstitutionBoundary : Set where
  constructor rsa260-production-substitution-boundary
  field
    syntheticDotPaid : Bool
    syntheticSpMVPaid : Bool
    syntheticKrylovPaid : Bool
    syntheticProjectionPaid : Bool
    syntheticGeneratorPaid : Bool
    syntheticNonzeroKernelRecoveryPaid : Bool
    productionMatrixShapePaidByPrimarySource : Bool
    productionKrylovCountPaidByPrimarySource : Bool
    productionGeneratorLengthPaidByPrimarySource : Bool
    productionKernelVectorCountPaidByPrimarySource : Bool
    productionDependencyCountPaidByPrimarySource : Bool
    productionMatrixBytesPaid : Bool
    productionCheckpointOrGeneratorBytesPaid : Bool
    exactModifiedSourceRevisionPaid : Bool
    productionCPUReplayPaid : Bool
    cudaParityPaid : Bool
    ncclParityPaid : Bool
    fullProductionLinearAlgebraReplayPaid : Bool
open RSA260ProductionSubstitutionBoundary public

currentRSA260ProductionSubstitutionBoundary : RSA260ProductionSubstitutionBoundary
currentRSA260ProductionSubstitutionBoundary = rsa260-production-substitution-boundary
  true true true true true true
  true true true true true
  false false false false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ProductionShapeImpliesProductionBytes : Set where
data SyntheticKernelImpliesProductionKernel : Set where
data SearchMissImpliesArtifactAbsent : Set where
data CPUReferenceImpliesCUDAParity : Set where
data CUDAParityImpliesNCCLParity : Set where
data DownstreamArtifactImpliesEarlierCarrier : Set where

authorReportedShapeDoesNotCreateBytes : ProductionShapeImpliesProductionBytes → ⊥
authorReportedShapeDoesNotCreateBytes ()

syntheticKernelDoesNotCreateProductionKernel : SyntheticKernelImpliesProductionKernel → ⊥
syntheticKernelDoesNotCreateProductionKernel ()

searchMissDoesNotProveAbsence : SearchMissImpliesArtifactAbsent → ⊥
searchMissDoesNotProveAbsence ()

cpuReferenceDoesNotCreateCUDAParity : CPUReferenceImpliesCUDAParity → ⊥
cpuReferenceDoesNotCreateCUDAParity ()

cudaParityDoesNotCreateNCCLParity : CUDAParityImpliesNCCLParity → ⊥
cudaParityDoesNotCreateNCCLParity ()

downstreamArtifactDoesNotCreateEarlierCarrier : DownstreamArtifactImpliesEarlierCarrier → ⊥
downstreamArtifactDoesNotCreateEarlierCarrier ()
