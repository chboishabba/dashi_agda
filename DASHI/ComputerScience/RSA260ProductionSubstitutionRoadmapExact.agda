module DASHI.ComputerScience.RSA260ProductionSubstitutionRoadmapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260KrylovKernelRecoveryExact as SyntheticLA
import DASHI.ComputerScience.RSA260GNFSRunParameterArtifactSnowballExact as RunArtifact
import DASHI.ComputerScience.RSA260ProductionArtifactSubstituteAdmissionExact as Substitute
import DASHI.ComputerScience.RSA260LACarrierBidiDerivationExact as BidiCarrier
import DASHI.ComputerScience.RSA260BidiCandidateExperimentExact as CandidateExperiment
import DASHI.ComputerScience.RSA260BidiCandidateBWCShadowExact as CandidateBWC

------------------------------------------------------------------------
-- RSA-260 PRODUCTION-SUBSTITUTION ROADMAP
--
-- The synthetic CPU Block-Wiedemann-shaped ladder is end-to-end through a
-- nonzero v with Mv=0.  The public production LA envelope has also been
-- intersected bidirectionally with downstream Block-Wiedemann/gather demands,
-- yielding a typed sparse-GF(2) carrier CONSTRAINT FIBRE.
--
-- A runnable implicit member of that fibre has passed carrier/held-out tests,
-- and a 924x512 shadow has passed an exact-byte BWC-shaped preparation test
-- using B = A A^T.  Neither result identifies the historical production bytes.
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
-- Prior/admission/bidi/experiment boundaries retained rather than collapsed.
------------------------------------------------------------------------

syntheticLABoundary : SyntheticLA.RSA260KrylovKernelRecoveryRoadmapBoundary
syntheticLABoundary = SyntheticLA.currentRSA260KrylovKernelRecoveryRoadmapBoundary

runArtifactBoundary : RunArtifact.RSA260RunParameterArtifactBoundary
runArtifactBoundary = RunArtifact.canonicalRSA260RunParameterArtifactBoundary

substituteAdmissionBoundary : Substitute.SubstituteAdmissionBoundary
substituteAdmissionBoundary = Substitute.currentSubstituteAdmissionBoundary

bidiCarrierBoundary : BidiCarrier.BidiCarrierDerivationBoundary
bidiCarrierBoundary = BidiCarrier.canonicalBidiCarrierDerivationBoundary

bidiDerivedCarrier : BidiCarrier.BidiDerivedLACarrierFibre
bidiDerivedCarrier = BidiCarrier.currentBidiDerivedLACarrierFibre

candidateExperimentBoundary : CandidateExperiment.CandidateConsumerSupportBoundary
candidateExperimentBoundary = CandidateExperiment.canonicalCandidateConsumerSupportBoundary

candidateExperimentReceipt : CandidateExperiment.CandidateExperimentExecutionReceipt
candidateExperimentReceipt = CandidateExperiment.currentCandidateExperimentExecutionReceipt

candidateBWCShadowBoundary : CandidateBWC.PreparedShadowConsumerBoundary
candidateBWCShadowBoundary = CandidateBWC.canonicalPreparedShadowConsumerBoundary

candidateBWCShadowReceipt : CandidateBWC.BWCShadowExecutionReceipt
candidateBWCShadowReceipt = CandidateBWC.currentBWCShadowExecutionReceipt

------------------------------------------------------------------------
-- Ordered residual router.
------------------------------------------------------------------------

data ProductionResidual : Set where
  acquireSameObjectMemberOfDerivedLACarrierFibre : ProductionResidual
  raiseCandidateProjectionWidthTowardProduction : ProductionResidual
  runCandidateMatrixGeneratorAndKernelRecovery : ProductionResidual
  acquireProductionProjectionCheckpointOrGenerator : ProductionResidual
  bindExactModifiedSourceRevision : ProductionResidual
  reproduceProductionCPUReference : ProductionResidual
  reproduceCUDAKernel : ProductionResidual
  reproduceNCCLDistribution : ProductionResidual
  reproduceFullRSA260LinearAlgebra : ProductionResidual

firstUnpaidProductionResidual : ProductionResidual
firstUnpaidProductionResidual = acquireSameObjectMemberOfDerivedLACarrierFibre

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

    bidiProductionLACarrierConstraintFibreDerived : Bool
    bidiProductionLACarrierUniqueInstanceDerived : Bool
    bidiExactCarrierBytesDerived : Bool

    runnableBidiCandidateImplemented : Bool
    runnableBidiCandidateProductionContractPassed : Bool
    runnableBidiCandidateHeldOutStructurePassed : Bool
    runnableBidiCandidateShadowLeftKernelPassed : Bool
    runnableBidiCandidatePreparedSquareAdapterPassed : Bool
    runnableBidiCandidatePackedScalarFactorizedKrylovPassed : Bool
    runnableBidiCandidateProjectionSequencePassed : Bool
    runnableBidiCandidateExactBWCShadowBlobExecuted : Bool
    runnableBidiCandidateHistoricalIdentityPaid : Bool
    runnableBidiCandidateProductionBWCReplayPaid : Bool

    productionMatrixBytesPaid : Bool
    productionCheckpointOrGeneratorBytesPaid : Bool
    exactModifiedSourceRevisionPaid : Bool
    productionCPUReplayPaid : Bool
    cudaParityPaid : Bool
    ncclParityPaid : Bool
    fullProductionLinearAlgebraReplayPaid : Bool
open RSA260ProductionSubstitutionBoundary public

currentRSA260ProductionSubstitutionBoundary : RSA260ProductionSubstitutionBoundary
currentRSA260ProductionSubstitutionBoundary = record
  { syntheticDotPaid = true
  ; syntheticSpMVPaid = true
  ; syntheticKrylovPaid = true
  ; syntheticProjectionPaid = true
  ; syntheticGeneratorPaid = true
  ; syntheticNonzeroKernelRecoveryPaid = true
  ; productionMatrixShapePaidByPrimarySource = true
  ; productionKrylovCountPaidByPrimarySource = true
  ; productionGeneratorLengthPaidByPrimarySource = true
  ; productionKernelVectorCountPaidByPrimarySource = true
  ; productionDependencyCountPaidByPrimarySource = true
  ; bidiProductionLACarrierConstraintFibreDerived = true
  ; bidiProductionLACarrierUniqueInstanceDerived = false
  ; bidiExactCarrierBytesDerived = false
  ; runnableBidiCandidateImplemented = true
  ; runnableBidiCandidateProductionContractPassed = true
  ; runnableBidiCandidateHeldOutStructurePassed = true
  ; runnableBidiCandidateShadowLeftKernelPassed = true
  ; runnableBidiCandidatePreparedSquareAdapterPassed = true
  ; runnableBidiCandidatePackedScalarFactorizedKrylovPassed = true
  ; runnableBidiCandidateProjectionSequencePassed = true
  ; runnableBidiCandidateExactBWCShadowBlobExecuted = true
  ; runnableBidiCandidateHistoricalIdentityPaid = false
  ; runnableBidiCandidateProductionBWCReplayPaid = false
  ; productionMatrixBytesPaid = false
  ; productionCheckpointOrGeneratorBytesPaid = false
  ; exactModifiedSourceRevisionPaid = false
  ; productionCPUReplayPaid = false
  ; cudaParityPaid = false
  ; ncclParityPaid = false
  ; fullProductionLinearAlgebraReplayPaid = false
  }

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ProductionShapeImpliesProductionBytes : Set where
data BidiCarrierFibreImpliesUniqueMatrix : Set where
data RunnableCandidateImpliesHistoricalMatrix : Set where
data PassedDeclaredExperimentImpliesProductionBWC : Set where
data AATShadowImpliesProductionPreparedEncoding : Set where
data SyntheticKernelImpliesProductionKernel : Set where
data SearchMissImpliesArtifactAbsent : Set where
data CPUReferenceImpliesCUDAParity : Set where
data CUDAParityImpliesNCCLParity : Set where
data DownstreamArtifactImpliesEarlierCarrier : Set where

authorReportedShapeDoesNotCreateBytes : ProductionShapeImpliesProductionBytes → ⊥
authorReportedShapeDoesNotCreateBytes ()

bidiCarrierFibreDoesNotCreateUniqueMatrix : BidiCarrierFibreImpliesUniqueMatrix → ⊥
bidiCarrierFibreDoesNotCreateUniqueMatrix ()

runnableCandidateDoesNotCreateHistoricalMatrix : RunnableCandidateImpliesHistoricalMatrix → ⊥
runnableCandidateDoesNotCreateHistoricalMatrix ()

passedExperimentDoesNotCreateProductionBWC : PassedDeclaredExperimentImpliesProductionBWC → ⊥
passedExperimentDoesNotCreateProductionBWC ()

aatShadowDoesNotCreateProductionPreparedEncoding : AATShadowImpliesProductionPreparedEncoding → ⊥
aatShadowDoesNotCreateProductionPreparedEncoding ()

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
