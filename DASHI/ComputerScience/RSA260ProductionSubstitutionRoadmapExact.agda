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
import DASHI.ComputerScience.RSA260BidiCandidateRobustnessExact as CandidateRobustness
import DASHI.ComputerScience.RSA260BidiPreparationFibreSearchExact as PreparationSearch
import DASHI.ComputerScience.RSA260BidiPreparationFrontierCrossValidationExact as PreparationFrontier
import DASHI.ComputerScience.RSA260CADOBlockWiedemannArtifactSchemaSnowballExact as CADOArtifacts
import DASHI.ComputerScience.RSA260BlockWiedemannProductionScaleReconstructionExact as ProductionScale
import DASHI.ComputerScience.RSA260BidiRandomIncidenceCarrierCrossValidationExact as RandomIncidence
import DASHI.ComputerScience.RSA260BidiCADOGridPermutationCrossValidationExact as CADOGrid
import DASHI.ComputerScience.RSA260BidiFineIncidencePredictorExact as FineIncidence
import DASHI.ComputerScience.RSA260BidiFineIncidenceInterpolationExact as FineInterpolation
import DASHI.ComputerScience.RSA260BidiTwoHopCommonNeighbourFibreExact as TwoHop
import DASHI.ComputerScience.RSA260BidiFineIncidenceDefectCoverageExact as DefectCoverage

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
    balancingPermutationBytesLocated : Bool
    exactSourceRevisionLocated : Bool
    exactExecutableDigestLocated : Bool
    targetedPublicSearchPerformed : Bool
    searchMissProvesNonexistence : Bool
open ProductionArtifactAcquisitionState public

currentProductionArtifactAcquisitionState : ProductionArtifactAcquisitionState
currentProductionArtifactAcquisitionState = production-artifact-acquisition-state
  false false false false false false false false true false

------------------------------------------------------------------------
-- Existing owners remain the authoritative coordinates.
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

candidateBWCShadowBoundary : CandidateBWC.PreparedShadowConsumerBoundary
candidateBWCShadowBoundary = CandidateBWC.canonicalPreparedShadowConsumerBoundary

candidateFullLABoundary : CandidateFullLA.CandidateFullLAConsumerBoundary
candidateFullLABoundary = CandidateFullLA.canonicalCandidateFullLAConsumerBoundary

candidateProjection256Boundary : CandidateProjection256.Projection256ConsumerBoundary
candidateProjection256Boundary = CandidateProjection256.canonicalProjection256ConsumerBoundary

candidateRobustnessBoundary : CandidateRobustness.CandidateRobustnessBoundary
candidateRobustnessBoundary = CandidateRobustness.canonicalCandidateRobustnessBoundary

preparationSearchBoundary : PreparationSearch.PreparationFibreInterpretationBoundary
preparationSearchBoundary = PreparationSearch.canonicalPreparationFibreInterpretationBoundary

preparationSearchReceipt : PreparationSearch.PreparationSearchReceipt
preparationSearchReceipt = PreparationSearch.currentPreparationSearchReceipt

preparationFrontierPreference : PreparationFrontier.RobustnessAwarePreparationPreference
preparationFrontierPreference = PreparationFrontier.currentRobustnessAwarePreparationPreference

cadoArtifactSchema : CADOArtifacts.CADOBlockWiedemannArtifactSchema
cadoArtifactSchema = CADOArtifacts.currentCADOBlockWiedemannArtifactSchema

productionScaleBoundary : ProductionScale.ProductionScaleReconstructionBoundary
productionScaleBoundary = ProductionScale.canonicalProductionScaleReconstructionBoundary

randomIncidenceBoundary : RandomIncidence.RandomIncidenceInterpretationBoundary
randomIncidenceBoundary = RandomIncidence.canonicalRandomIncidenceInterpretationBoundary

cadoGridBoundary : CADOGrid.CADOGridInterpretationBoundary
cadoGridBoundary = CADOGrid.canonicalCADOGridInterpretationBoundary

fineIncidenceBoundary : FineIncidence.FineIncidencePredictorBoundary
fineIncidenceBoundary = FineIncidence.canonicalFineIncidencePredictorBoundary

fineInterpolationBoundary : FineInterpolation.FineIncidenceFragilityBoundary
fineInterpolationBoundary = FineInterpolation.canonicalFineIncidenceFragilityBoundary

twoHopBoundary : TwoHop.TwoHopInterpretationBoundary
twoHopBoundary = TwoHop.canonicalTwoHopInterpretationBoundary

defectCoverageBoundary : DefectCoverage.DefectCoverageInterpretationBoundary
defectCoverageBoundary = DefectCoverage.canonicalDefectCoverageInterpretationBoundary

------------------------------------------------------------------------
-- Ordered residual routers.
------------------------------------------------------------------------

data ProductionResidual : Set where
  acquireSameObjectFineIncidenceBearingLACarrierArtifact : ProductionResidual
  acquireSameObjectMemberOfDerivedLACarrierFibre : ProductionResidual
  recoverSameObjectBalancingPermutation : ProductionResidual
  acquireProductionProjectionCheckpointOrGenerator : ProductionResidual
  bindExactModifiedSourceRevision : ProductionResidual
  reproduceProductionCPUReference : ProductionResidual
  reproduceCUDAKernel : ProductionResidual
  reproduceNCCLDistribution : ProductionResidual
  reproduceFullRSA260LinearAlgebra : ProductionResidual

firstUnpaidProductionResidual : ProductionResidual
firstUnpaidProductionResidual = acquireSameObjectFineIncidenceBearingLACarrierArtifact

data CandidateExperimentResidual : Set where
  replicateDefectCoverageCurveAcrossPerturbationSeeds : CandidateExperimentResidual
  fitCoverageAwareRecurrenceComplexityFromStructuralFibrePortfolio : CandidateExperimentResidual
  exactByteExecutePreparationSearchClosure : CandidateExperimentResidual
  measureCandidateCompressionCostFrontier : CandidateExperimentResidual
  validateCandidateAgainstSameObjectProductionArtifact : CandidateExperimentResidual

firstUnpaidCandidateExperimentResidual : CandidateExperimentResidual
firstUnpaidCandidateExperimentResidual = replicateDefectCoverageCurveAcrossPerturbationSeeds

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
    cadoArtifactFilenameSchemaPaid : Bool
    cadoBalancingPermutationShapePaid : Bool
    productionGeneratorScaleFormulaReconstructed : Bool
    productionKrylovEndpointFormulaReconstructed : Bool
    exactProductionCADORevisionRecovered : Bool
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
    runnableBidiCandidateSeedRobustnessPaid : Bool
    runnableBidiCandidateAdapterRobustnessPaid : Bool
    runnableBidiCandidatePreparationFibreSearchPaid : Bool
    runnableBidiCandidatePreparationSearchExactBlobPaid : Bool
    runnableBidiCandidateFrontierCrossSeedPaid : Bool
    runnableBidiCandidateFrontierWidth256Paid : Bool
    runnableBidiCandidateFrontierExactBlobPaid : Bool
    runnableBidiCandidateRobustPreferredPreparationIdentified : Bool
    randomFineIncidenceCrossValidationPaid : Bool
    randomFineIncidenceConsumerRecoveredAfterEscalation : Bool
    cadoShapedBalancingCrossValidationPaid : Bool
    fineIncidenceFamilyPredictorPaid : Bool
    fineIncidenceInterpolationPaid : Bool
    oneSwapPerRowFragilityEnsemblePaid : Bool
    oneSwapProjectionCrossPaid : Bool
    twoHopCommonNeighbourFibresPaid : Bool
    defectCoverageCurvePaid : Bool
    defectCoverageSeedReplicationPaid : Bool
    broadCoverageRaisesRecurrenceComplexity : Bool
    sameCoarseContractDeterminesRecurrenceComplexity : Bool
    fineIncidenceMeasuredOnProductionMatrix : Bool
    sameObjectFineIncidenceArtifactPaid : Bool
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
  ; cadoArtifactFilenameSchemaPaid = true
  ; cadoBalancingPermutationShapePaid = true
  ; productionGeneratorScaleFormulaReconstructed = true
  ; productionKrylovEndpointFormulaReconstructed = true
  ; exactProductionCADORevisionRecovered = false
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
  ; runnableBidiCandidateSeedRobustnessPaid = true
  ; runnableBidiCandidateAdapterRobustnessPaid = true
  ; runnableBidiCandidatePreparationFibreSearchPaid = true
  ; runnableBidiCandidatePreparationSearchExactBlobPaid = false
  ; runnableBidiCandidateFrontierCrossSeedPaid = true
  ; runnableBidiCandidateFrontierWidth256Paid = true
  ; runnableBidiCandidateFrontierExactBlobPaid = false
  ; runnableBidiCandidateRobustPreferredPreparationIdentified = true
  ; randomFineIncidenceCrossValidationPaid = true
  ; randomFineIncidenceConsumerRecoveredAfterEscalation = true
  ; cadoShapedBalancingCrossValidationPaid = true
  ; fineIncidenceFamilyPredictorPaid = true
  ; fineIncidenceInterpolationPaid = true
  ; oneSwapPerRowFragilityEnsemblePaid = true
  ; oneSwapProjectionCrossPaid = true
  ; twoHopCommonNeighbourFibresPaid = true
  ; defectCoverageCurvePaid = true
  ; defectCoverageSeedReplicationPaid = false
  ; broadCoverageRaisesRecurrenceComplexity = true
  ; sameCoarseContractDeterminesRecurrenceComplexity = false
  ; fineIncidenceMeasuredOnProductionMatrix = false
  ; sameObjectFineIncidenceArtifactPaid = false
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

data ProductionShapeImpliesProductionBytes : Set where
data BidiCarrierFibreImpliesUniqueMatrix : Set where
data RunnableCandidateImpliesHistoricalMatrix : Set where
data PreparationFrontierImpliesProductionAdapter : Set where
data SparseKernelImpliesFactoringSpeedup : Set where
data PythonTimingImpliesProductionPerformance : Set where
data FormulaReconstructionImpliesExactRevision : Set where
data SyntheticFineIncidencePredictorImpliesProductionMeasurement : Set where
data DefectCoverageCurveImpliesUniversalThreshold : Set where
data SameCoarseContractImpliesSameRecurrenceComplexity : Set where
data SearchMissImpliesArtifactAbsent : Set where

authorReportedShapeDoesNotCreateBytes : ProductionShapeImpliesProductionBytes → ⊥
authorReportedShapeDoesNotCreateBytes ()

bidiCarrierFibreDoesNotCreateUniqueMatrix : BidiCarrierFibreImpliesUniqueMatrix → ⊥
bidiCarrierFibreDoesNotCreateUniqueMatrix ()

runnableCandidateDoesNotCreateHistoricalMatrix : RunnableCandidateImpliesHistoricalMatrix → ⊥
runnableCandidateDoesNotCreateHistoricalMatrix ()

preparationFrontierDoesNotCreateProductionAdapter : PreparationFrontierImpliesProductionAdapter → ⊥
preparationFrontierDoesNotCreateProductionAdapter ()

sparseKernelDoesNotCreateFactoringSpeedup : SparseKernelImpliesFactoringSpeedup → ⊥
sparseKernelDoesNotCreateFactoringSpeedup ()

pythonTimingDoesNotCreateProductionPerformance : PythonTimingImpliesProductionPerformance → ⊥
pythonTimingDoesNotCreateProductionPerformance ()

formulaReconstructionDoesNotCreateExactRevision : FormulaReconstructionImpliesExactRevision → ⊥
formulaReconstructionDoesNotCreateExactRevision ()

syntheticFineIncidenceDoesNotCreateProductionMeasurement : SyntheticFineIncidencePredictorImpliesProductionMeasurement → ⊥
syntheticFineIncidenceDoesNotCreateProductionMeasurement ()

defectCoverageDoesNotCreateUniversalThreshold : DefectCoverageCurveImpliesUniversalThreshold → ⊥
defectCoverageDoesNotCreateUniversalThreshold ()

sameCoarseContractDoesNotCreateSameRecurrence : SameCoarseContractImpliesSameRecurrenceComplexity → ⊥
sameCoarseContractDoesNotCreateSameRecurrence ()

searchMissDoesNotProveAbsence : SearchMissImpliesArtifactAbsent → ⊥
searchMissDoesNotProveAbsence ()
