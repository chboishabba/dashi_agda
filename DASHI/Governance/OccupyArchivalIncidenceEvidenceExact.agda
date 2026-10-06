module DASHI.Governance.OccupyArchivalIncidenceEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- OCCUPY ARCHIVAL INCIDENCE EVIDENCE.
--
-- Provenance class: PRIMARY ARCHIVAL MATERIAL / ARCHIVAL COLLECTION METADATA.
--
-- This owner does not infer a participant x issue matrix from attendee lists.
-- A participation-edge candidate is admitted only when the inspected source
-- explicitly associates a named participant with a named issue/proposal in the
-- bounded meeting record.  Facilitation, attendance and agenda presence remain
-- distinct relations.
------------------------------------------------------------------------

record ArchivalCollectionReference : Set where
  constructor archivalCollectionReference
  field
    collectionLabel : String
    repositoryInstitution : String
    sourceURL : String
    boundedRole : String

open ArchivalCollectionReference public

nycgaArchivedWebsite : ArchivalCollectionReference
nycgaArchivedWebsite =
  archivalCollectionReference
    "New York City General Assembly archived website"
    "Tamiment Library and Robert F. Wagner Labor Archives, New York University"
    "https://findingaids.library.nyu.edu/tamwag/tam_630/"
    "archive metadata states that the NYCGA website contains General Assembly meeting minutes, proposals, working-group material and activist resources; availability does not establish completeness or truth"

owsArchivesWorkingGroupRecords : ArchivalCollectionReference
owsArchivesWorkingGroupRecords =
  archivalCollectionReference
    "Occupy Wall Street Archives Working Group Records"
    "Tamiment Library and Robert F. Wagner Labor Archives, New York University"
    "https://findingaids.library.nyu.edu/tamwag/tam_583/"
    "collection metadata documents General Assembly, Spokes Council and working-group decisions, notes, proposals and organizational material; collection scope does not convert every record into a vote transcript"

kinnaPrichardOccupyDataset : ArchivalCollectionReference
kinnaPrichardOccupyDataset =
  archivalCollectionReference
    "Archival and workshop materials relating to constitutional practices in grass roots anarchistic organisations 2011-2018"
    "UK Data Service ReShare"
    "https://reshare.ukdataservice.ac.uk/853098/"
    "dataset includes statements and General Assembly minutes from Occupy Wall Street, Occupy London St Paul's and Occupy Oakland; corpus availability is not participant-level incidence completeness"

peopleLibraryMinutes : ArchivalCollectionReference
peopleLibraryMinutes =
  archivalCollectionReference
    "Occupy Wall Street Library Working Group minutes, 22 October 2011"
    "People's Library / Occupy Wall Street archival web record"
    "https://peopleslibrary.wordpress.com/2011/10/23/library-working-group-meeting-minutes-102211/"
    "bounded working-group meeting record with named participants, facilitation roles, agenda items and named speakers; it is not a NYCGA-wide population census"

canonicalOccupyArchivalCollections : List ArchivalCollectionReference
canonicalOccupyArchivalCollections =
  nycgaArchivedWebsite
  ∷ owsArchivesWorkingGroupRecords
  ∷ kinnaPrichardOccupyDataset
  ∷ peopleLibraryMinutes
  ∷ []

------------------------------------------------------------------------
-- Typed source relation.
------------------------------------------------------------------------

data ArchivalInteractionKind : Set where
  attendanceOnly : ArchivalInteractionKind
  facilitationRole : ArchivalInteractionKind
  minuteTakingRole : ArchivalInteractionKind
  namedSpeakerOnIssue : ArchivalInteractionKind
  namedQuestionOrResponseOnIssue : ArchivalInteractionKind
  explicitRecordedVote : ArchivalInteractionKind

data EvidenceScope : Set where
  workingGroupMeetingScope : EvidenceScope
  generalAssemblyScope : EvidenceScope
  spokesCouncilScope : EvidenceScope
  collectionMetadataScope : EvidenceScope

record ArchivalIncidenceCandidate : Set where
  constructor archivalIncidenceCandidate
  field
    sourceCollection : ArchivalCollectionReference
    meetingDate : String
    scope : EvidenceScope
    participantLabel : String
    issueLabel : String
    interactionKind : ArchivalInteractionKind
    sourceAnchor : String
    paysParticipationEdge : Bool
    paysParticipationEdgeJustification : String

open ArchivalIncidenceCandidate public

------------------------------------------------------------------------
-- One bounded real interaction witness from the 22 Oct 2011 Library Working
-- Group minutes.  The source names Adash from Structure as a speaker on the
-- Spokes Council proposal.  This pays only the relation:
--
--   named participant --addressed--> named issue
--
-- in that working-group meeting.  It does not pay a vote, stance, agreement,
-- NYCGA-wide representation, or a complete issue-participation matrix.
------------------------------------------------------------------------

adashSpokesCouncilCandidate : ArchivalIncidenceCandidate
adashSpokesCouncilCandidate =
  archivalIncidenceCandidate
    peopleLibraryMinutes
    "2011-10-22"
    workingGroupMeetingScope
    "Adash (Structure)"
    "Spokes Council proposal"
    namedSpeakerOnIssue
    "Library Working Group minutes identify Adash from Structure as speaking about the Spokes Council proposal"
    true
    "the source explicitly associates the named speaker with the named proposal; only a bounded participation edge is paid"

------------------------------------------------------------------------
-- Non-edge examples: useful for preventing cross-product fabrication.
------------------------------------------------------------------------

steveFacilitationCandidate : ArchivalIncidenceCandidate
steveFacilitationCandidate =
  archivalIncidenceCandidate
    peopleLibraryMinutes
    "2011-10-22"
    workingGroupMeetingScope
    "Steve S."
    "meeting process"
    facilitationRole
    "minutes identify Steve S. as facilitator"
    false
    "facilitation is a process role and does not by itself prove participation on any substantive issue"

record OccupyArchivalIncidenceBoundary : Set where
  constructor occupyArchivalIncidenceBoundary
  field
    archiveAvailabilityPaid : Bool
    namedSourceAnchoredIssueInteractionCanPayBoundedEdge : Bool

    attendanceImpliesIssueParticipation : Bool
    facilitatorRoleImpliesSubstantiveIssueParticipation : Bool
    agendaMentionImpliesDecision : Bool
    archivedProposalImpliesAdoption : Bool
    minutesAssumedCompleteTranscript : Bool
    workingGroupEvidenceGeneralisesToAllOWS : Bool
    boundedCandidateCreatesCompleteIncidenceMatrix : Bool
    archivePaysQuantitativeScalingLaw : Bool
    archivalEdgeCreatesPoliticalAuthority : Bool

open OccupyArchivalIncidenceBoundary public

canonicalOccupyArchivalIncidenceBoundary : OccupyArchivalIncidenceBoundary
canonicalOccupyArchivalIncidenceBoundary =
  occupyArchivalIncidenceBoundary
    true
    true
    false
    false
    false
    false
    false
    false
    false
    false
    false

canonicalOccupyArchivalIncidenceReceipt : GenericReceipt.GenericReceipt
canonicalOccupyArchivalIncidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "source-bounded Occupy archival incidence evidence"
    "DASHI.Governance.OccupyArchivalIncidenceEvidenceExact"
    "canonicalOccupyArchivalIncidenceBoundary"
    "registers archival collections containing OWS minutes/proposals and admits one bounded named-speaker-to-proposal interaction candidate only where the inspected minutes explicitly associate the participant and issue"
    "attendance, facilitation, agenda inclusion and archival presence do not manufacture issue participation, votes, complete matrices, movement-wide generalisation, scaling laws or political authority"
    "agda -i . DASHI/Governance/OccupyArchivalIncidenceEvidenceRegression.agda"
