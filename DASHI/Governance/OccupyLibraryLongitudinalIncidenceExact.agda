module DASHI.Governance.OccupyLibraryLongitudinalIncidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyParticipantPseudonymisationExact as Privacy

------------------------------------------------------------------------
-- LONGITUDINAL ARCHIVAL INCIDENCE FAMILY, PSEUDONYMISED.
--
-- Primary archival source:
-- People's Library / Occupy Wall Street Library Working Group minutes.
-- https://peopleslibrary.wordpress.com/the-working-group/working-group-meeting-minutes/
-- plus the dedicated 22 October 2011 minutes page.
--
-- Each participant label below is a stable keyed-HMAC pseudonym produced by
-- DASHI's privacy layer. Public source anchors are retained, but raw person
-- names are intentionally not propagated into this derived table.
------------------------------------------------------------------------

data MeetingId : Set where
  oct22Meeting nov20Meeting nov28Meeting dec04Meeting dec11Meeting jan08Meeting mar11Meeting : MeetingId

record LongitudinalEdge : Set where
  constructor longitudinalEdge
  field
    meeting : MeetingId
    participantToken : Privacy.ParticipantToken
    issueLabel : String
    sourceAnchor : String
open LongitudinalEdge public

edgeCount : List LongitudinalEdge → Nat
edgeCount [] = 0
edgeCount (_ ∷ rest) = suc (edgeCount rest)

oct22URL : String
oct22URL = "https://peopleslibrary.wordpress.com/2011/10/22/library-working-group-meeting-minutes/"
minutesIndexURL : String
minutesIndexURL = "https://peopleslibrary.wordpress.com/the-working-group/working-group-meeting-minutes/"

oct22Edges : List LongitudinalEdge
oct22Edges =
  longitudinalEdge oct22Meeting Privacy.p-ebddda "Spokes Council proposal" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-442ac6 "Finance integration" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-aeedd2 "Finance integration" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-81d19f "Library budget" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-33f894 "Finance integration" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-2b47b2 "Silent Reading technology" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-81d19f "Silent Reading technology" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-aeedd2 "Silent Reading technology" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-61309c "Electricity / generator" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-33f894 "Electricity / generator" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-33f894 "Town planning / shelter" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-a936c6 "Town planning / shelter" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-b64222 "Town planning / shelter" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-442ac6 "Guest-speaker coordination" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-bc1911 "Guest-speaker coordination" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-b64222 "Zines / pamphlets" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-fc55c2 "Zines / pamphlets" oct22URL
  ∷ longitudinalEdge oct22Meeting Privacy.p-442ac6 "Printed governance archive" oct22URL
  ∷ []

nov20Edges : List LongitudinalEdge
nov20Edges =
  longitudinalEdge nov20Meeting Privacy.p-232026 "legal representation / Norman Siegel" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting Privacy.p-aeedd2 "meeting-location communication failure" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting Privacy.p-aeedd2 "occupied office allocation" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting Privacy.p-fc55c2 "recovered books / evidence handling" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting Privacy.p-f0412f "mirror catalogue proposal" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting Privacy.p-aeedd2 "email-list and blog membership proposal" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting Privacy.p-f0412f "blog comment policy" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting Privacy.p-81d19f "Library 3.0 / portable-action practice" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting Privacy.p-a936c6 "Finance transparency / Spokes Council reportback" minutesIndexURL
  ∷ []

nov28Edges : List LongitudinalEdge
nov28Edges =
  longitudinalEdge nov28Meeting Privacy.p-3d9d51 "team cohesion / communication" minutesIndexURL
  ∷ longitudinalEdge nov28Meeting Privacy.p-fc55c2 "book count and recovered-book processing" minutesIndexURL
  ∷ longitudinalEdge nov28Meeting Privacy.p-232026 "legal action against city" minutesIndexURL
  ∷ longitudinalEdge nov28Meeting Privacy.p-f4f5bb "community accountability proposal" minutesIndexURL
  ∷ longitudinalEdge nov28Meeting Privacy.p-c3fe3a "future library infrastructure" minutesIndexURL
  ∷ longitudinalEdge nov28Meeting Privacy.p-33f894 "squat / physical-space proposal" minutesIndexURL
  ∷ longitudinalEdge nov28Meeting Privacy.p-f4f5bb "storage and processing of new books" minutesIndexURL
  ∷ []

dec11Edges : List LongitudinalEdge
dec11Edges =
  longitudinalEdge dec11Meeting Privacy.p-a936c6 "Free Literature cargo-bike proposal" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting Privacy.p-614e70 "Free Literature cargo-bike proposal" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting Privacy.p-16fcb5 "Free Literature cargo-bike proposal" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting Privacy.p-fc55c2 "Free Literature cargo-bike proposal" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting Privacy.p-81d19f "Free Literature cargo-bike proposal" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting Privacy.p-81d19f "open letter after Love Your Librarian Awards" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting Privacy.p-c3fe3a "Occupy office exclusivity concern" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting Privacy.p-649768 "book pickup and drop-off" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting Privacy.p-a936c6 "Hyperallergic book pickup" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting Privacy.p-c3fe3a "ALA representation concern" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting Privacy.p-f4f5bb "Occupy Writers support / statement" minutesIndexURL
  ∷ []

jan08Edges : List LongitudinalEdge
jan08Edges =
  longitudinalEdge jan08Meeting Privacy.p-33f894 "shopping carts for mobile actions" minutesIndexURL
  ∷ longitudinalEdge jan08Meeting Privacy.p-649768 "Spokes Council dysfunction / participation" minutesIndexURL
  ∷ longitudinalEdge jan08Meeting Privacy.p-33f894 "Spokes Council procedural proposal" minutesIndexURL
  ∷ longitudinalEdge jan08Meeting Privacy.p-3d9d51 "innovative-libraries conference representation" minutesIndexURL
  ∷ longitudinalEdge jan08Meeting Privacy.p-a936c6 "bookstore solidarity / distributed library space" minutesIndexURL
  ∷ longitudinalEdge jan08Meeting Privacy.p-7d95b2 "Staten Island public squat / library donations" minutesIndexURL
  ∷ longitudinalEdge jan08Meeting Privacy.p-33f894 "WePay / accounting point-person work" minutesIndexURL
  ∷ []

appendEdges : List LongitudinalEdge → List LongitudinalEdge → List LongitudinalEdge
appendEdges [] ys = ys
appendEdges (x ∷ xs) ys = x ∷ appendEdges xs ys

longitudinalObservedEdges : List LongitudinalEdge
longitudinalObservedEdges =
  appendEdges oct22Edges (appendEdges nov20Edges (appendEdges nov28Edges (appendEdges dec11Edges jan08Edges)))

canonicalLongitudinalObservedEdgeCount : edgeCount longitudinalObservedEdges ≡ 52
canonicalLongitudinalObservedEdgeCount = refl

data ProcessObservationKind : Set where
  shorterFusesAndNastierEmailThreads discussionBreakdown majorityMeetingTimeSpentInMediation manyAgendaItemsTabledByMediation almostEntireMeetingSpentOnConflict explicitBureaucracyFrustration : ProcessObservationKind

data ProcessBurdenObserved : MeetingId → ProcessObservationKind → Set where
  nov28CommunicationStrain : ProcessBurdenObserved nov28Meeting shorterFusesAndNastierEmailThreads
  nov28Breakdown : ProcessBurdenObserved nov28Meeting discussionBreakdown
  dec04MajorityMediation : ProcessBurdenObserved dec04Meeting majorityMeetingTimeSpentInMediation
  dec04AgendaTabled : ProcessBurdenObserved dec04Meeting manyAgendaItemsTabledByMediation
  dec04AlmostEntireMeetingConflict : ProcessBurdenObserved dec04Meeting almostEntireMeetingSpentOnConflict
  mar11BureaucracyFrustration : ProcessBurdenObserved mar11Meeting explicitBureaucracyFrustration

nov28IncidenceAndBreakdownCooccur :
  (edgeCount nov28Edges ≡ 7) × ProcessBurdenObserved nov28Meeting discussionBreakdown
nov28IncidenceAndBreakdownCooccur = refl , nov28Breakdown

record LongitudinalIncidenceBoundary : Set where
  constructor longitudinalIncidenceBoundary
  field
    rowsAreArchivalCodingNotParticipantFormalism repeatedSamePersonIssueUtterancesCollapsed processObservationsSeparatedFromIncidenceRows pseudonymousParticipantTokensUsed rawNamesPropagatedIntoDerivedRows attendanceAgendaCrossProductPromoted interactionRowEncodesAgreement interactionRowEncodesVote incidenceCountIsImportance incidenceCountIsSpeakingTime processObservationIsCoordinationCost incidenceCountCausallyExplainsBurden descriptiveCooccurrenceIsCausalIdentification selectedMeetingsAreCompleteOWSCorpus sourceMinutesAssumedCompleteTranscripts longitudinalFamilyCreatesPoliticalAuthority : Bool
open LongitudinalIncidenceBoundary public

canonicalLongitudinalBoundary : LongitudinalIncidenceBoundary
canonicalLongitudinalBoundary =
  longitudinalIncidenceBoundary true true true true false false false false false false false false false false false false

canonicalOccupyLibraryLongitudinalIncidenceReceipt : GenericReceipt.GenericReceipt
canonicalOccupyLibraryLongitudinalIncidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "pseudonymised longitudinal People's Library archival incidence family"
    "DASHI.Governance.OccupyLibraryLongitudinalIncidenceExact"
    "canonicalLongitudinalBoundary"
    "codes fifty-two explicit participant-to-topic archival rows across five selected People's Library meetings using stable collision-audited participant pseudonyms and separately records source-reported process strain"
    "raw person names are not propagated into derived rows; source anchors remain public; selected graph rows are not a complete OWS corpus, coordination-cost measure, causal scaling law, or political authority"
    "agda -i . DASHI/Governance/OccupyLibraryLongitudinalIncidenceRegression.agda"
