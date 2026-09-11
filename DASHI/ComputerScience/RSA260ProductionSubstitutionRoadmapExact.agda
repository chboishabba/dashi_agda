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
import DASHI.ComputerScience.RSA260BidiCandidateGeneratorKernelExact as CandidateFullLA
import DASHI.ComputerScience.RSA260BidiCandidateProjection256Exact as CandidateProjection256

------------------------------------------------------------------------
-- RSA-260 PRODUCTION-SUBSTITUTION ROADMAP
--
-- The historical identity route remains unpaid at the byte level.  In
-- parallel, the bidi-derived carrier fibre now has a runnable implicit member
-- whose executable shadow has passed carrier, held-out, left-kernel, prepared
-- SpMV/Krylov/projection, shared-generator, kernel-recovery and width-256
-- transport/projection consumers.
--
-- Candidate adequacy for those declared consumers is not historical identity.
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
  656182601 656182189 98431741898
  "150.0 nonzeros per row (reported density)"
  2564096 2 256 256 1281607 40 64 26 12
  "cuda" "nccl" true

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

candidateFullLABoundary : CandidateFullLA.CandidateFullLAConsumerBoundary
candidateFullLABoundary = CandidateFullLA.canonicalCandidateFullLAConsumerBoundary

candidateGeneratorReceipt : CandidateFullLA.CandidateGeneratorExecutionReceipt
candidateGeneratorReceipt = CandidateFullLA.currentCandidateGeneratorExecutionReceipt

candidateKernelReceipt : CandidateFullLA.CandidateKernelExecutionReceipt
candidateKernelReceipt = CandidateFullLA.currentCandidateKernelExecutionReceipt

candidateProjection256Boundary : CandidateProjection256.Projection256ConsumerBoundary
candidateProjection256Boundary = CandidateProjection256.canonicalProjection256ConsumerBoundary

candidateProjection256Receipt : CandidateProjection256.Projection256ExecutionReceipt
candidateProjection256Receipt = CandidateProjection256.currentProjection256ExecutionReceipt

------------------------------------------------------------------------
-- Ordered residual routers.
------------------------------------------------------------------------

data ProductionResidual : Set where
  acquireSameObjectMemberOfDerivedLACarrierFibre : ProductionResidual
  acquireProductionProjectionCheckpointOrGenerator : ProductionResidual
  bindExactModifiedSourceRevision : ProductionResidual
  reproduceProductionCPUReference : ProductionResidual
  reproduceCUDAKernel : ProductionResidual
  reproduceNCCLDistribution : ProductionResidual
  reproduceFullRSA260LinearAlgebra : ProductionResidual

firstUnpaidProductionResidual : ProductionResidual
firstUnpaidProductionResidual = acquireSameObjectMemberOfDerivedLACarrierFibre

data CandidateExperimentResidual : Set where
  compareIndependentProjectionSeeds : CandidateExperimentResidual
  scaleGeneratorConsumerBeyondWidth8 : CandidateExperimentResidual
  compareAlternativePreparationAdapters : CandidateExperimentResidual
  measureCandidateCompressionCostFrontier : CandidateExperimentResidual
  validateCandidateAgainstSameObjectProductionArtifact : CandidateExperimentResidual

firstUnpaidCandidateExperimentResidual : CandidateExperimentResidual
firstUnpaidCandidateExperimentResidual = compareIndependentProjectionSeeds

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
    runnableBidiCandidateSharedGeneratorPaid : Bool
    runnableBidiCandidateGeneratorWithheldValidationPaid : Bool
    runnableBidiCandidateShiftedRelationSpacePaid : Bool
    runnableBidiCandidateNonzeroKernelRecoveryPaid : Bool
    runnableBidiCandidateKernelVerifiedBackOnOriginalAT : Bool
    runnableBidiCandidateExactGeneratorKernelBlobExecuted : Bool
    runnableBidiCandidateTwoWidth256SequencesPaid : Bool
    runnableBidiCandidateTotal512BlockColumnsPaid : Bool
    runnableBidiCandidateWidth256ExplicitFactorizedParityPaid : Bool
    runnableBidiCandidateExactProjection256BlobExecuted : Bool
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
  ; runnableBidiCandidateSharedGeneratorPaid = true
  ; runnableBidiCandidateGeneratorWithheldValidationPaid = true
  ; runnableBidiCandidateShiftedRelationSpacePaid = true
  ; runnableBidiCandidateNonzeroKernelRecoveryPaid = true
  ; runnableBidiCandidateKernelVerifiedBackOnOriginalAT = true
  ; runnableBidiCandidateExactGeneratorKernelBlobExecuted = true
  ; runnableBidiCandidateTwoWidth256SequencesPaid = true
  ; runnableBidiCandidateTotal512BlockColumnsPaid = true
  ; runnableBidiCandidateWidth256ExplicitFactorizedParityPaid = true
  ; runnableBidiCandidateExactProjection256BlobExecuted = true
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
data CandidateGeneratorImpliesProductionGenerator : Set where
data CandidateKernelImpliesProductionDependency : Set where
data Width256CandidateImpliesProductionProjection : Set where
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

candidateGeneratorDoesNotCreateProductionGenerator : CandidateGeneratorImpliesProductionGenerator → ⊥
candidateGeneratorDoesNotCreateProductionGenerator ()

candidateKernelDoesNotCreateProductionDependency : CandidateKernelImpliesProductionDependency → ⊥
candidateKernelDoesNotCreateProductionDependency ()

width256CandidateDoesNotCreateProductionProjection : Width256CandidateImpliesProductionProjection → ⊥
width256CandidateDoesNotCreateProductionProjection ()

searchMissDoesNotProveAbsence : SearchMissImpliesArtifactAbsent → ⊥
searchMissDoesNotProveAbsence ()

cpuReferenceDoesNotCreateCUDAParity : CPUReferenceImpliesCUDAParity → ⊥
cpuReferenceDoesNotCreateCUDAParity ()

cudaParityDoesNotCreateNCCLParity : CUDAParityImpliesNCCLParity → ⊥
cudaParityDoesNotCreateNCCLParity ()

downstreamArtifactDoesNotCreateEarlierCarrier : DownstreamArtifactImpliesEarlierCarrier → ⊥
downstreamArtifactDoesNotCreateEarlierCarrier ()
