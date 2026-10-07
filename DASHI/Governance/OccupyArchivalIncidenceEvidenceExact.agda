module DASHI.Governance.OccupyArchivalIncidenceEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyParticipantPseudonymisationExact as Privacy

record ArchivalCollectionReference : Set where
  constructor archivalCollectionReference
  field
    collectionLabel repositoryInstitution sourceURL boundedRole : String
open ArchivalCollectionReference public

nycgaArchivedWebsite : ArchivalCollectionReference
nycgaArchivedWebsite = archivalCollectionReference
  "New York City General Assembly at #OccupyWallStreet Archived Website"
  "Tamiment Library and Robert F. Wagner Labor Archives, New York University"
  "https://findingaids.library.nyu.edu/tamwag/web_arc_003/contents/aspace_ref1107/"
  "archive metadata states that the NYCGA website contains General Assembly meeting minutes, proposals, working-group material and activist resources; availability does not establish completeness or truth"

owsArchivesWorkingGroupRecords : ArchivalCollectionReference
owsArchivesWorkingGroupRecords = archivalCollectionReference
  "Occupy Wall Street Archives Working Group Records"
  "Tamiment Library and Robert F. Wagner Labor Archives, New York University"
  "https://findingaids.library.nyu.edu/tamwag/tam_630/"
  "collection metadata documents General Assembly, Spokes Council and working-group decisions, notes, proposals and organizational material; collection scope does not convert every record into a vote transcript"

kinnaPrichardOccupyDataset : ArchivalCollectionReference
kinnaPrichardOccupyDataset = archivalCollectionReference
  "Archival and workshop materials relating to constitutional practices in grass roots anarchistic organisations 2011-2018"
  "UK Data Service ReShare"
  "https://reshare.ukdataservice.ac.uk/853247/"
  "dataset includes statements and General Assembly minutes from Occupy Wall Street, Occupy London St Paul's and Occupy Oakland; corpus availability is not participant-level incidence completeness"

peopleLibraryMinutes : ArchivalCollectionReference
peopleLibraryMinutes = archivalCollectionReference
  "Occupy Wall Street Library Working Group minutes, 22 October 2011"
  "People's Library / Occupy Wall Street archival web record"
  "https://peopleslibrary.wordpress.com/2011/10/22/library-working-group-meeting-minutes/"
  "bounded working-group meeting record with participant/facilitation roles, agenda items and speakers; it is not a NYCGA-wide population census"

canonicalOccupyArchivalCollections : List ArchivalCollectionReference
canonicalOccupyArchivalCollections = nycgaArchivedWebsite ∷ owsArchivesWorkingGroupRecords ∷ kinnaPrichardOccupyDataset ∷ peopleLibraryMinutes ∷ []

data ArchivalInteractionKind : Set where
  attendanceOnly facilitationRole minuteTakingRole namedSpeakerOnIssue namedQuestionOrResponseOnIssue explicitRecordedVote : ArchivalInteractionKind

data EvidenceScope : Set where
  workingGroupMeetingScope generalAssemblyScope spokesCouncilScope collectionMetadataScope : EvidenceScope

record ArchivalIncidenceCandidate : Set where
  constructor archivalIncidenceCandidate
  field
    sourceCollection : ArchivalCollectionReference
    meetingDate : String
    scope : EvidenceScope
    participantToken : Privacy.ParticipantToken
    issueLabel : String
    interactionKind : ArchivalInteractionKind
    sourceAnchor : String
    paysParticipationEdge : Bool
    paysParticipationEdgeJustification : String
open ArchivalIncidenceCandidate public

boundedSpeakerProposalCandidate : ArchivalIncidenceCandidate
boundedSpeakerProposalCandidate = archivalIncidenceCandidate
  peopleLibraryMinutes
  "2011-10-22"
  workingGroupMeetingScope
  Privacy.p-ebddda
  "Spokes Council proposal"
  namedSpeakerOnIssue
  "Library Working Group minutes explicitly associate the pseudonymised source participant with the Spokes Council proposal"
  true
  "the source explicitly associates that participant with the proposal; only a bounded participation edge is paid"

facilitationOnlyCandidate : ArchivalIncidenceCandidate
facilitationOnlyCandidate = archivalIncidenceCandidate
  peopleLibraryMinutes
  "2011-10-22"
  workingGroupMeetingScope
  Privacy.p-442ac6
  "meeting process"
  facilitationRole
  "minutes identify the pseudonymised source participant as facilitator"
  false
  "facilitation is a process role and does not by itself prove participation on any substantive issue"

record OccupyArchivalIncidenceBoundary : Set where
  constructor occupyArchivalIncidenceBoundary
  field
    archiveAvailabilityPaid namedSourceAnchoredIssueInteractionCanPayBoundedEdge pseudonymousTokensUsed rawNamesPropagatedIntoDerivedCandidates attendanceImpliesIssueParticipation facilitatorRoleImpliesSubstantiveIssueParticipation agendaMentionImpliesDecision archivedProposalImpliesAdoption minutesAssumedCompleteTranscript workingGroupEvidenceGeneralisesToAllOWS boundedCandidateCreatesCompleteIncidenceMatrix archivePaysQuantitativeScalingLaw archivalEdgeCreatesPoliticalAuthority : Bool
open OccupyArchivalIncidenceBoundary public

canonicalOccupyArchivalIncidenceBoundary : OccupyArchivalIncidenceBoundary
canonicalOccupyArchivalIncidenceBoundary = occupyArchivalIncidenceBoundary
  true true true false false false false false false false false false false

canonicalOccupyArchivalIncidenceReceipt : GenericReceipt.GenericReceipt
canonicalOccupyArchivalIncidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "source-bounded pseudonymised Occupy archival incidence evidence"
    "DASHI.Governance.OccupyArchivalIncidenceEvidenceExact"
    "canonicalOccupyArchivalIncidenceBoundary"
    "registers archival collections and admits a bounded participant-to-proposal interaction candidate only where inspected minutes explicitly associate the source participant and issue, using an opaque stable participant token in derived state"
    "raw person names are not propagated; attendance, facilitation, agenda inclusion and archival presence do not manufacture issue participation, votes, complete matrices, movement-wide generalisation, scaling laws or political authority"
    "agda -i . DASHI/Governance/OccupyArchivalIncidenceEvidenceRegression.agda"
