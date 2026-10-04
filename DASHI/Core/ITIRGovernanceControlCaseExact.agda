module DASHI.Core.ITIRGovernanceControlCaseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

-- Orthogonal lifecycle coordinates.
data ServiceChangeState : Set where
  proposed implemented verified validated released observed incident rolledBack : ServiceChangeState

data EvidenceState : Set where
  sourceWritten compileChecked fixtureChecked runtimeObserved productionObserved : EvidenceState

record GovernanceControlCase : Set where
  constructor governance-control-case
  field
    controlCaseRef : String
    subjectRef : String
    obligationRefs : List String
    scopeRefs : List String
    accountableOwnerRefs : List String
    riskRefs : List String
    controlRefs : List String
    implementationRefs : List String
    evidenceRefs : List String
    residualRefs : List String
    serviceChangeState : ServiceChangeState
    evidenceState : EvidenceState

    sourceStandardsAreDesignLenses : Bool
    sourceStandardsAreDesignLensesIsTrue : sourceStandardsAreDesignLenses ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsReviewAuthority : Bool
    createsReviewAuthorityIsFalse : createsReviewAuthority ≡ false
    createsCertificationAuthority : Bool
    createsCertificationAuthorityIsFalse : createsCertificationAuthority ≡ false
    createsAccessAuthority : Bool
    createsAccessAuthorityIsFalse : createsAccessAuthority ≡ false
open GovernanceControlCase public

record InformationAsset : Set where
  constructor information-asset
  field
    assetRef : String
    dataClassRef : String
    containsPII : Bool
    sensitivityRef : String
    accountableRoleRef : String
    purposeRef : String
    matterRef : String
    accessBasisRef : String
    allowedConsumerRefs : List String
    storageRef : String
    externalProviderRefs : List String
    retentionClassRef : String
    revocationOrDeletionStateRef : String
    auditRefs : List String
    createsMatterVisibility : Bool
    createsMatterVisibilityIsFalse : createsMatterVisibility ≡ false
open InformationAsset public

record ProcessingActivity : Set where
  constructor processing-activity
  field
    activityRef : String
    purposeRef : String
    inputAssetRefs : List String
    outputAssetRefs : List String
    processorRoleRef : String
    externalProviderRefs : List String
    controlRefs : List String
    evidenceRefs : List String
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
open ProcessingActivity public

data NonconformanceKind : Set where
  semanticMismatch provenanceLoss authorityLeak scopeLeak privacyExposure
  securityBoundaryViolation uiAmbiguity replayNondeterminism
  performanceRegression hiddenWorkAmplification : NonconformanceKind

record Nonconformance : Set where
  constructor nonconformance
  field
    nonconformanceRef : String
    subjectRef : String
    defectKind : NonconformanceKind
    requirementRefs : List String
    evidenceRefs : List String
    residualRefs : List String
    rootCauseRefs : List String
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
open Nonconformance public

record CAPACycle : Set where
  constructor capa-cycle
  field
    capaRef : String
    nonconformance : Nonconformance
    defineRefs : List String
    measureRefs : List String
    analyseRefs : List String
    improveRefs : List String
    controlRefs : List String
    originalResidualRefs : List String
    originalEvidenceRefs : List String
    erasesOriginalNonconformance : Bool
    erasesOriginalNonconformanceIsFalse : erasesOriginalNonconformance ≡ false
open CAPACycle public

-- Invalid collapses are explicitly uninhabited.
data ImplementedMeansValidated : Set where
data CompileCheckedMeansRuntimeObserved : Set where
data PassingControlMeansCertified : Set where
data ControlEvidenceCreatesTruth : Set where
data GovernancePriorityCreatesUserPriority : Set where
data InformationAssetGrantsMatterVisibility : Set where
data CAPAErasesOriginalResidual : Set where

implementedDoesNotMeanValidated : ImplementedMeansValidated → ⊥
implementedDoesNotMeanValidated ()

compileDoesNotMeanRuntime : CompileCheckedMeansRuntimeObserved → ⊥
compileDoesNotMeanRuntime ()

passingDoesNotMeanCertified : PassingControlMeansCertified → ⊥
passingDoesNotMeanCertified ()

controlEvidenceDoesNotCreateTruth : ControlEvidenceCreatesTruth → ⊥
controlEvidenceDoesNotCreateTruth ()

governanceDoesNotCreateUserPriority : GovernancePriorityCreatesUserPriority → ⊥
governanceDoesNotCreateUserPriority ()

assetMetadataDoesNotGrantMatterVisibility : InformationAssetGrantsMatterVisibility → ⊥
assetMetadataDoesNotGrantMatterVisibility ()

capaDoesNotEraseOriginalResidual : CAPAErasesOriginalResidual → ⊥
capaDoesNotEraseOriginalResidual ()

record GOV1Boundary : Set where
  constructor gov1-boundary
  field
    oneCrossRepositoryControlPlane : Bool
    oneCrossRepositoryControlPlaneIsTrue : oneCrossRepositoryControlPlane ≡ true
    separateISOOrITILSemanticSubsystems : Bool
    separateISOOrITILSemanticSubsystemsIsFalse : separateISOOrITILSemanticSubsystems ≡ false
    standardsCertificationClaimed : Bool
    standardsCertificationClaimedIsFalse : standardsCertificationClaimed ≡ false
    serviceAndEvidenceStatesOrthogonal : Bool
    serviceAndEvidenceStatesOrthogonalIsTrue : serviceAndEvidenceStatesOrthogonal ≡ true
    governanceScalarizesINV : Bool
    governanceScalarizesINVIsFalse : governanceScalarizesINV ≡ false

canonicalGOV1Boundary : GOV1Boundary
canonicalGOV1Boundary =
  gov1-boundary
    true refl
    false refl
    false refl
    true refl
    false refl
