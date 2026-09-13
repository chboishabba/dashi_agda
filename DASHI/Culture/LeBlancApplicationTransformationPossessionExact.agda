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

------------------------------------------------------------------------
-- DOI-bearing pre-death publication object distinct from the later NASA webinar.
------------------------------------------------------------------------

record LeBlancPublicationCarrier : Set where
  constructor leblanc-publication-carrier
  field
    title : String
    authors : String
    venue : String
    doi : String
    eventDate : String
    publicationState : String
    sourceClass : String
    qid : String
    deweyTraversal : String
    exactPublicationIdentityPaid : Bool
    sameObjectAsNTRS20250008475Paid : Bool
    publicationImpliesPostLossRoleState : Bool

open LeBlancPublicationCarrier public

leblancSpaceFissionGaps2025 : LeBlancPublicationCarrier
leblancSpaceFissionGaps2025 = leblanc-publication-carrier
  "Space Fission Instrumentation and Control Technology Gaps"
  "N. Dianne Bull Ezell; Tyler Steiner; Joshua LeBlanc; Jarvis Caffrey"
  "Proceedings of Nuclear Plant Instrumentation and Control and Human-Machine Interface Technology, NPIC&HMIT 2025"
  "10.13182/NPICHMIT25-46370"
  "2025-06-15 through 2025-06-18"
  "published 2025; pages 1694-1701; American Nuclear Society"
  "primary/near-primary peer-reviewed conference proceedings metadata"
  "unresolvedQid"
  "621 Applied physics / 629 Other branches of engineering"
  true false false

record RoleSnapshotChronology : Set where
  constructor role-snapshot-chronology
  field deathDate : String; ntrsAcquisitionDate : String; webinarDate : String; slideStillNamesLeBlanc : Bool; acquisitionDateDeterminesRoleStateDate : Bool; webinarDateDeterminesRoleStateDate : Bool; internalFreezeOrAuthorshipDateLocated : Bool; firstPostLossGovernanceArtifactLocated : Bool
open RoleSnapshotChronology public

canonicalRoleSnapshotChronology = role-snapshot-chronology
  "2025-07-22" "2025-08-16" "2025-08-26"
  true false false false false

------------------------------------------------------------------------
-- Repository-metadata archaeology.
--
-- The NTRS citation surface for 20250008475 was still maintained after the
-- event: it currently records Last Modified = 2026-07-16 while the attached
-- deck continues to contain the 2025 recognition slide naming LeBlanc as SNP
-- I&C TechMat Team Lead.  A repository-page maintenance timestamp therefore
-- cannot be treated as evidence that embedded programme-role content was
-- contemporaneously refreshed.
------------------------------------------------------------------------

record RepositoryMetadataRoleStateBoundary : Set where
  constructor repository-metadata-role-state-boundary
  field
    ntrsDocumentId : String
    deathDate : String
    ntrsAcquisitionDate : String
    webinarDate : String
    repositoryLastModifiedDate : String
    embeddedRoleLabelStillPresent : Bool
    repositoryModificationAfterDeath : Bool
    repositoryModificationAfterWebinar : Bool
    repositoryModificationImpliesEmbeddedRoleRefresh : Bool
    repositoryModificationDeterminesSuccessor : Bool
    boundedReading : String

open RepositoryMetadataRoleStateBoundary public

canonicalRepositoryMetadataRoleStateBoundary : RepositoryMetadataRoleStateBoundary
canonicalRepositoryMetadataRoleStateBoundary = repository-metadata-role-state-boundary
  "20250008475"
  "2025-07-22"
  "2025-08-16"
  "2025-08-26"
  "2026-07-16"
  true true true false false
  "NTRS repository metadata was modified long after LeBlanc's death and after the webinar, while the attached 2025 deck still displays his TechMat role label. This pays repository-maintenance chronology only; it does not date the slide's internal authorship/freeze state, prove that the role roster was refreshed, or identify a successor."

------------------------------------------------------------------------
-- Genuine post-loss programme continuity, but not TechMat-role succession.
------------------------------------------------------------------------

record PostLossProgramContinuityLead : Set where
  constructor post-loss-program-continuity-lead
  field datedPostLossSurface : String; continuingLead : String; continuingRole : String; primarySourceReference : String; supplementarySourceReference : String; programmeContinuitySupported : Bool; exactLeBlancRoleSuccessionPaid : Bool; predecessorRoleAlreadyDistinctFromLeBlanc : Bool
open PostLossProgramContinuityLead public

okojieSeptember2025ContinuityLead = post-loss-program-continuity-lead
  "2025-09-24 FSP Technology Maturation webinar / close-out"
  "Robert S. Okojie"
  "Lead NASA FSP Instrumentation and Controls / NASA FSP I&C Lead"
  "Idaho National Laboratory Fission Surface Power programme page: Recent Updates & Events, FSP Technology Maturation Webinar held 2025-09-24 with I&C testing updates"
  "Robert Okojie public professional post describing the 2025-09-24 close-out presentation; NASA NTRS 20250008475 August recognition slide already lists Okojie as NASA FSP I&C Lead and LeBlanc separately as NASA SNP I&C TechMat Team Lead"
  true false true

------------------------------------------------------------------------
-- Same-WBS continuity across the loss boundary.
--
-- NTRS 20250008475 and NTRS 20240010391 both carry WBS
-- 658133.04.01.22.01.06.  The latter is a different Glenn-authored FSP sensor
-- presentation whose meeting date is 2026-05-27, well after LeBlanc's death.
-- This pays continuity of the programme/WBS carrier, not continuity of
-- LeBlanc's person-specific TechMat role or a successor identity.
------------------------------------------------------------------------

record PostLossWBSContinuityState : Set where
  constructor post-loss-wbs-continuity-state
  field
    wbs : String
    leblancNtrsObject : String
    leblancObjectAcquired : String
    laterNtrsObject : String
    laterObjectAuthor : String
    laterObjectMeetingDate : String
    sameWbsPaid : Bool
    laterMeetingPostLoss : Bool
    programmeCarrierContinuityPaid : Bool
    personRoleContinuityPaid : Bool
    techMatSuccessorIdentityPaid : Bool
    sameWbsImpliesSameOwner : Bool
    boundedReading : String

open PostLossWBSContinuityState public

canonicalPostLossWBSContinuityState : PostLossWBSContinuityState
canonicalPostLossWBSContinuityState = post-loss-wbs-continuity-state
  "658133.04.01.22.01.06"
  "NTRS 20250008475 — NASA 40 kW Fission Surface Power I&C Technology Development Path"
  "2025-08-16"
  "NTRS 20240010391 — Thin Film Sensors for Fission Surface Power"
  "John D Wrbanek, NASA Glenn Research Center"
  "2026-05-27"
  true true true false false false
  "The identical WBS persists in a distinct NASA FSP technical object with a 2026 meeting date, proving programme/resource-carrier continuity after LeBlanc's death. The later object has a different author and topic and therefore does not pay LeBlanc role continuity, TechMat succession, or same-owner identity."

record LeBlancApplicationBoundary : Set where
  constructor leblanc-application-boundary
  field techMatLeadImpliesSoleQualificationOwner : Bool; executiveCommitteeMembershipImpliesUniqueKnowledge : Bool; technologyMaturationRoleSourceBacked : Bool; failureMapOwnershipClosed : Bool; postLossPublicationImpliesPostLossActiveRole : Bool; staleRecognitionSlideImpliesNoSuccessor : Bool; datedPostLossGovernanceArtifactRequiredForSuccession : Bool; postLossProgramContinuityImpliesTechMatSuccession : Bool; alreadyDistinctFSPLeadMayBeCalledTechMatSuccessorWithoutReceipt : Bool; doiPublicationEqualsNTRSWebinarManifestation : Bool; laterRepositoryMetadataUpdateImpliesRoleRefresh : Bool
open LeBlancApplicationBoundary public

canonicalLeBlancApplicationBoundary = leblanc-application-boundary
  false false true false false false true false false false false

data LeBlancApplicationReverseTarget : Set where
  acquireTechMatWorkBreakdown acquireQualificationTestOwnership acquireFailureEnvelopeOwnership acquireCalibrationDriftOwnership acquireRecognitionSlideFreezeDate acquireFirstPostLossICGovernanceArtifact acquireExactPostLossTechMatRoleRoster acquireSuccessorOrHandover acquireRequalificationDelayOrRework : LeBlancApplicationReverseTarget

firstLeBlancSuccessionTarget = acquireRecognitionSlideFreezeDate
postLossContinuityNextTarget = acquireExactPostLossTechMatRoleRoster
