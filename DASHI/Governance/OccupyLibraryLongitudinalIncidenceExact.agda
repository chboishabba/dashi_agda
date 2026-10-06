module DASHI.Governance.OccupyLibraryLongitudinalIncidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- LONGITUDINAL REAL ARCHIVAL INCIDENCE FAMILY.
--
-- Primary archival source:
-- People's Library / Occupy Wall Street Library Working Group minutes.
-- https://peopleslibrary.wordpress.com/the-working-group/working-group-meeting-minutes/
-- plus the dedicated 22 October 2011 minutes page.
--
-- Attribution / coding rule:
--   * each edge below is a DASHI archival coding of an explicit named-person
--     -> named agenda/proposal/topic association visible in the minutes;
--   * the coding is not attributed to the meeting participants;
--   * attendance, facilitation and agenda presence are not cross-producted;
--   * repeated utterances by the same person on the same issue are collapsed
--     to one bounded incidence row in this descriptive graph;
--   * process-burden observations are held in a different relation and do not
--     become a causal consequence of incidence count.
------------------------------------------------------------------------

data MeetingId : Set where
  oct22Meeting : MeetingId
  nov20Meeting : MeetingId
  nov28Meeting : MeetingId
  dec04Meeting : MeetingId
  dec11Meeting : MeetingId
  jan08Meeting : MeetingId
  mar11Meeting : MeetingId

record LongitudinalEdge : Set where
  constructor longitudinalEdge
  field
    meeting : MeetingId
    participantLabel : String
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

------------------------------------------------------------------------
-- 22 October 2011: same admitted relation surface as the separately typed
-- finite specimen, repeated here as strings only so the longitudinal family
-- has one uniform carrier.  This is not a second independent source.
------------------------------------------------------------------------

oct22Edges : List LongitudinalEdge
oct22Edges =
  longitudinalEdge oct22Meeting "Adash (Structure)" "Spokes Council proposal" oct22URL
  ∷ longitudinalEdge oct22Meeting "Steve S." "Finance integration" oct22URL
  ∷ longitudinalEdge oct22Meeting "Betsy" "Finance integration" oct22URL
  ∷ longitudinalEdge oct22Meeting "Stephen" "Library budget" oct22URL
  ∷ longitudinalEdge oct22Meeting "Frances" "Finance integration" oct22URL
  ∷ longitudinalEdge oct22Meeting "Orion" "Silent Reading technology" oct22URL
  ∷ longitudinalEdge oct22Meeting "Stephen" "Silent Reading technology" oct22URL
  ∷ longitudinalEdge oct22Meeting "Betsy" "Silent Reading technology" oct22URL
  ∷ longitudinalEdge oct22Meeting "Eric" "Electricity / generator" oct22URL
  ∷ longitudinalEdge oct22Meeting "Frances" "Electricity / generator" oct22URL
  ∷ longitudinalEdge oct22Meeting "Frances" "Town planning / shelter" oct22URL
  ∷ longitudinalEdge oct22Meeting "Sean" "Town planning / shelter" oct22URL
  ∷ longitudinalEdge oct22Meeting "Thaddeus" "Town planning / shelter" oct22URL
  ∷ longitudinalEdge oct22Meeting "Steve S." "Guest-speaker coordination" oct22URL
  ∷ longitudinalEdge oct22Meeting "Michael" "Guest-speaker coordination" oct22URL
  ∷ longitudinalEdge oct22Meeting "Thaddeus" "Zines / pamphlets" oct22URL
  ∷ longitudinalEdge oct22Meeting "Zach" "Zines / pamphlets" oct22URL
  ∷ longitudinalEdge oct22Meeting "Steve S." "Printed governance archive" oct22URL
  ∷ []

------------------------------------------------------------------------
-- 20 November 2011.
-- Source section explicitly names the people attached to these reportbacks,
-- proposals or discussion topics.  Rows do not encode stance or agreement.
------------------------------------------------------------------------

nov20Edges : List LongitudinalEdge
nov20Edges =
  longitudinalEdge nov20Meeting "Bill" "legal representation / Norman Siegel" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting "Betsy" "meeting-location communication failure" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting "Betsy" "occupied office allocation" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting "Zach" "recovered books / evidence handling" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting "Briar" "mirror catalogue proposal" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting "Betsy" "email-list and blog membership proposal" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting "Briar" "blog comment policy" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting "Stephen" "Library 3.0 / portable-action practice" minutesIndexURL
  ∷ longitudinalEdge nov20Meeting "Sean" "Finance transparency / Spokes Council reportback" minutesIndexURL
  ∷ []

------------------------------------------------------------------------
-- 28 November 2011.
------------------------------------------------------------------------

nov28Edges : List LongitudinalEdge
nov28Edges =
  longitudinalEdge nov28Meeting "Danny" "team cohesion / communication" minutesIndexURL
  ∷ longitudinalEdge nov28Meeting "Zach" "book count and recovered-book processing" minutesIndexURL
  ∷ longitudinalEdge nov28Meeting "Bill" "legal action against city" minutesIndexURL
  ∷ longitudinalEdge nov28Meeting "Michele" "community accountability proposal" minutesIndexURL
  ∷ longitudinalEdge nov28Meeting "Scales" "future library infrastructure" minutesIndexURL
  ∷ longitudinalEdge nov28Meeting "Frances" "squat / physical-space proposal" minutesIndexURL
  ∷ longitudinalEdge nov28Meeting "Michele" "storage and processing of new books" minutesIndexURL
  ∷ []

------------------------------------------------------------------------
-- 11 December 2011.
------------------------------------------------------------------------

dec11Edges : List LongitudinalEdge
dec11Edges =
  longitudinalEdge dec11Meeting "Sean" "Free Literature cargo-bike proposal" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting "Thadeaus" "Free Literature cargo-bike proposal" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting "Colin" "Free Literature cargo-bike proposal" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting "Zach" "Free Literature cargo-bike proposal" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting "Stephen" "Free Literature cargo-bike proposal" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting "Stephen" "open letter after Love Your Librarian Awards" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting "Scales" "Occupy office exclusivity concern" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting "Charlie" "book pickup and drop-off" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting "Sean" "Hyperallergic book pickup" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting "Scales" "ALA representation concern" minutesIndexURL
  ∷ longitudinalEdge dec11Meeting "Michele" "Occupy Writers support / statement" minutesIndexURL
  ∷ []

------------------------------------------------------------------------
-- 8 January 2012.
------------------------------------------------------------------------

jan08Edges : List LongitudinalEdge
jan08Edges =
  longitudinalEdge jan08Meeting "Frances" "shopping carts for mobile actions" minutesIndexURL
  ∷ longitudinalEdge jan08Meeting "Charlie" "Spokes Council dysfunction / participation" minutesIndexURL
  ∷ longitudinalEdge jan08Meeting "Frances" "Spokes Council procedural proposal" minutesIndexURL
  ∷ longitudinalEdge jan08Meeting "Danny" "innovative-libraries conference representation" minutesIndexURL
  ∷ longitudinalEdge jan08Meeting "Sean" "bookstore solidarity / distributed library space" minutesIndexURL
  ∷ longitudinalEdge jan08Meeting "Tim" "Staten Island public squat / library donations" minutesIndexURL
  ∷ longitudinalEdge jan08Meeting "Frances" "WePay / accounting point-person work" minutesIndexURL
  ∷ []

------------------------------------------------------------------------
-- Longitudinal family.  Appending is defined locally to avoid treating counts
-- as anything more than the admitted archival coding surface.
------------------------------------------------------------------------

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

longitudinalObservedEdges : List LongitudinalEdge
longitudinalObservedEdges =
  oct22Edges ++ nov20Edges ++ nov28Edges ++ dec11Edges ++ jan08Edges

canonicalLongitudinalObservedEdgeCount :
  edgeCount longitudinalObservedEdges ≡ 52
canonicalLongitudinalObservedEdgeCount = refl

------------------------------------------------------------------------
-- Separate archival process-observation relation.
--
-- These are what the minutes report about meeting process.  They are not
-- participant-level edges and are not a cost function.  In particular, this
-- module proves no causal relation from incidence count/degree to strain.
------------------------------------------------------------------------

data ProcessObservationKind : Set where
  shorterFusesAndNastierEmailThreads : ProcessObservationKind
  discussionBreakdown : ProcessObservationKind
  majorityMeetingTimeSpentInMediation : ProcessObservationKind
  manyAgendaItemsTabledByMediation : ProcessObservationKind
  almostEntireMeetingSpentOnConflict : ProcessObservationKind
  explicitBureaucracyFrustration : ProcessObservationKind


data ProcessBurdenObserved : MeetingId → ProcessObservationKind → Set where
  nov28CommunicationStrain :
    ProcessBurdenObserved nov28Meeting shorterFusesAndNastierEmailThreads
  nov28Breakdown :
    ProcessBurdenObserved nov28Meeting discussionBreakdown

  dec04MajorityMediation :
    ProcessBurdenObserved dec04Meeting majorityMeetingTimeSpentInMediation
  dec04AgendaTabled :
    ProcessBurdenObserved dec04Meeting manyAgendaItemsTabledByMediation
  dec04AlmostEntireMeetingConflict :
    ProcessBurdenObserved dec04Meeting almostEntireMeetingSpentOnConflict

  mar11BureaucracyFrustration :
    ProcessBurdenObserved mar11Meeting explicitBureaucracyFrustration

------------------------------------------------------------------------
-- Attribution / inference firewall.
------------------------------------------------------------------------

record LongitudinalIncidenceBoundary : Set where
  constructor longitudinalIncidenceBoundary
  field
    rowsAreArchivalCodingNotParticipantFormalism : Bool
    repeatedSamePersonIssueUtterancesCollapsed : Bool
    processObservationsSeparatedFromIncidenceRows : Bool

    attendanceAgendaCrossProductPromoted : Bool
    interactionRowEncodesAgreement : Bool
    interactionRowEncodesVote : Bool
    incidenceCountIsImportance : Bool
    incidenceCountIsSpeakingTime : Bool
    processObservationIsCoordinationCost : Bool
    incidenceCountCausallyExplainsBurden : Bool
    selectedMeetingsAreCompleteOWSCorpus : Bool
    sourceMinutesAssumedCompleteTranscripts : Bool
    longitudinalFamilyCreatesPoliticalAuthority : Bool

open LongitudinalIncidenceBoundary public

canonicalLongitudinalBoundary : LongitudinalIncidenceBoundary
canonicalLongitudinalBoundary =
  longitudinalIncidenceBoundary
    true
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
    false

canonicalOccupyLibraryLongitudinalIncidenceReceipt : GenericReceipt.GenericReceipt
canonicalOccupyLibraryLongitudinalIncidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "longitudinal People's Library archival incidence family"
    "DASHI.Governance.OccupyLibraryLongitudinalIncidenceExact"
    "canonicalLongitudinalBoundary"
    "codes fifty-two explicit named-person-to-topic archival rows across five selected People's Library meetings and separately records source-reported process strain from later meeting minutes"
    "the selected graph family is not a complete OWS corpus; row counts are not importance, speaking time or coordination cost, and the coexistence of incidence structure with process-strain observations proves no causal scaling law"
    "agda -i . DASHI/Governance/OccupyLibraryLongitudinalIncidenceRegression.agda"
