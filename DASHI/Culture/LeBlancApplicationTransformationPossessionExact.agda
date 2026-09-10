module DASHI.Culture.LeBlancApplicationTransformationPossessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

data PossessionStatus : Set where sourceBacked partial notLocated : PossessionStatus
record ApplicationRoleReceipt : Set where
  constructor application-role-receipt
  field roleOrPerson : String; transformationCoordinates : List T.TransformationCoordinate; status : PossessionStatus; sourceReference : String; boundedReading : String
open ApplicationRoleReceipt public

leblancTechMatRole : ApplicationRoleReceipt
leblancTechMatRole = application-role-receipt "Joshua LeBlanc / NASA SNP I&C TechMat Team Lead"
  (T.qualificationEvidence ∷ T.operatingWindow ∷ T.validationCorpus ∷ T.integrationWorkflow ∷ []) sourceBacked
  "NASA NTRS 20250008475 recognition slide; document acquired 2025-08-16 for 2025-08-26 FSP Technology Maturation webinar"
  "The source names LeBlanc as SNP I&C technology-maturation team lead. Because NTRS acquisition and webinar dates post-date his 2025-07-22 death, this is a role-snapshot carrier whose internal freeze/authorship date must be recovered before it can be used as a post-loss governance state. It supports a maturation/qualification role, not sole ownership of every component, test, or failure model."

leblancFailureMapOwnership : ApplicationRoleReceipt
leblancFailureMapOwnership = application-role-receipt "Joshua LeBlanc"
  (T.failureHistory ∷ T.uncertaintyModel ∷ T.calibrationState ∷ []) notLocated
  "bounded NASA public record"
  "No public receipt located here establishes person-specific ownership of component failure envelopes, calibration-drift datasets, accelerated-life models, or system-level probability-of-failure analysis."

record RoleSnapshotChronology : Set where
  constructor role-snapshot-chronology
  field
    deathDate : String
    ntrsAcquisitionDate : String
    webinarDate : String
    slideStillNamesLeBlanc : Bool
    acquisitionDateDeterminesRoleStateDate : Bool
    webinarDateDeterminesRoleStateDate : Bool
    internalFreezeOrAuthorshipDateLocated : Bool
    firstPostLossGovernanceArtifactLocated : Bool

open RoleSnapshotChronology public

canonicalRoleSnapshotChronology : RoleSnapshotChronology
canonicalRoleSnapshotChronology = role-snapshot-chronology
  "2025-07-22" "2025-08-16" "2025-08-26"
  true false false false false

record LeBlancApplicationBoundary : Set where
  constructor leblanc-application-boundary
  field
    techMatLeadImpliesSoleQualificationOwner : Bool
    executiveCommitteeMembershipImpliesUniqueKnowledge : Bool
    technologyMaturationRoleSourceBacked : Bool
    failureMapOwnershipClosed : Bool
    postLossPublicationImpliesPostLossActiveRole : Bool
    staleRecognitionSlideImpliesNoSuccessor : Bool
    datedPostLossGovernanceArtifactRequiredForSuccession : Bool

open LeBlancApplicationBoundary public

canonicalLeBlancApplicationBoundary : LeBlancApplicationBoundary
canonicalLeBlancApplicationBoundary = leblanc-application-boundary
  false false true false false false true

data LeBlancApplicationReverseTarget : Set where
  acquireTechMatWorkBreakdown
  acquireQualificationTestOwnership
  acquireFailureEnvelopeOwnership
  acquireCalibrationDriftOwnership
  acquireRecognitionSlideFreezeDate
  acquireFirstPostLossICGovernanceArtifact
  acquireSuccessorOrHandover
  acquireRequalificationDelayOrRework : LeBlancApplicationReverseTarget

firstLeBlancSuccessionTarget : LeBlancApplicationReverseTarget
firstLeBlancSuccessionTarget = acquireRecognitionSlideFreezeDate
