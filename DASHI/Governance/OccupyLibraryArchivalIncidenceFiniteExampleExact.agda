module DASHI.Governance.OccupyLibraryArchivalIncidenceFiniteExampleExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- REAL BOUNDED FINITE INCIDENCE EXAMPLE.
--
-- Primary archival source:
-- People's Library / Occupy Wall Street Library Working Group minutes,
-- 22 October 2011.
-- https://peopleslibrary.wordpress.com/2011/10/22/library-working-group-meeting-minutes/
--
-- Attribution rule:
--   * constructors below encode only explicit named utterance -> agenda/proposal
--     associations visible in the inspected minutes;
--   * consensus/temp-check outcomes are represented by a distinct relation;
--   * no attendance x agenda cross-product is generated;
--   * no speaker edge is interpreted as agreement, vote, mandate or authority.
------------------------------------------------------------------------

data Participant : Set where
  adash : Participant
  steve : Participant
  betsy : Participant
  stephen : Participant
  frances : Participant
  eric : Participant
  orion : Participant
  sean : Participant
  thaddeus : Participant
  michael : Participant
  zach : Participant


data Issue : Set where
  spokesCouncilProposal : Issue
  financeIntegration : Issue
  libraryBudget : Issue
  silentReadingTechnology : Issue
  electricityGenerator : Issue
  townPlanningShelter : Issue
  guestSpeakerCoordination : Issue
  zinesAndPamphlets : Issue
  printedGovernanceArchive : Issue
  meetingTime : Issue
  libraryClosingTime : Issue

------------------------------------------------------------------------
-- Explicit source-paid participant -> issue relations.
------------------------------------------------------------------------

data ExplicitInteraction : Participant → Issue → Set where
  adashSpokes : ExplicitInteraction adash spokesCouncilProposal

  steveFinance : ExplicitInteraction steve financeIntegration
  betsyFinance : ExplicitInteraction betsy financeIntegration
  stephenBudget : ExplicitInteraction stephen libraryBudget
  francesFinance : ExplicitInteraction frances financeIntegration

  orionSilentReading : ExplicitInteraction orion silentReadingTechnology
  stephenSilentReading : ExplicitInteraction stephen silentReadingTechnology
  betsySilentReading : ExplicitInteraction betsy silentReadingTechnology

  ericGenerator : ExplicitInteraction eric electricityGenerator
  francesGenerator : ExplicitInteraction frances electricityGenerator

  francesTownPlanning : ExplicitInteraction frances townPlanningShelter
  seanTownPlanning : ExplicitInteraction sean townPlanningShelter
  thaddeusTownPlanning : ExplicitInteraction thaddeus townPlanningShelter

  steveGuestSpeakers : ExplicitInteraction steve guestSpeakerCoordination
  michaelGuestSpeakers : ExplicitInteraction michael guestSpeakerCoordination

  thaddeusZines : ExplicitInteraction thaddeus zinesAndPamphlets
  zachZines : ExplicitInteraction zach zinesAndPamphlets

  stevePrintedArchive : ExplicitInteraction steve printedGovernanceArchive

------------------------------------------------------------------------
-- Finite row carrier used only to audit the explicitly admitted source rows.
------------------------------------------------------------------------

record ObservedEdge : Set where
  constructor observedEdge
  field
    participant : Participant
    issue : Issue
    witness : ExplicitInteraction participant issue

open ObservedEdge public

canonicalObservedEdges : List ObservedEdge
canonicalObservedEdges =
  observedEdge adash spokesCouncilProposal adashSpokes
  ∷ observedEdge steve financeIntegration steveFinance
  ∷ observedEdge betsy financeIntegration betsyFinance
  ∷ observedEdge stephen libraryBudget stephenBudget
  ∷ observedEdge frances financeIntegration francesFinance
  ∷ observedEdge orion silentReadingTechnology orionSilentReading
  ∷ observedEdge stephen silentReadingTechnology stephenSilentReading
  ∷ observedEdge betsy silentReadingTechnology betsySilentReading
  ∷ observedEdge eric electricityGenerator ericGenerator
  ∷ observedEdge frances electricityGenerator francesGenerator
  ∷ observedEdge frances townPlanningShelter francesTownPlanning
  ∷ observedEdge sean townPlanningShelter seanTownPlanning
  ∷ observedEdge thaddeus townPlanningShelter thaddeusTownPlanning
  ∷ observedEdge steve guestSpeakerCoordination steveGuestSpeakers
  ∷ observedEdge michael guestSpeakerCoordination michaelGuestSpeakers
  ∷ observedEdge thaddeus zinesAndPamphlets thaddeusZines
  ∷ observedEdge zach zinesAndPamphlets zachZines
  ∷ observedEdge steve printedGovernanceArchive stevePrintedArchive
  ∷ []

edgeCount : List ObservedEdge → Nat
edgeCount [] = 0
edgeCount (_ ∷ rest) = suc (edgeCount rest)

canonicalObservedEdgeCount : edgeCount canonicalObservedEdges ≡ 18
canonicalObservedEdgeCount = refl

------------------------------------------------------------------------
-- Descriptive incidence degrees.
--
-- These are exact counts for the finite admitted row set above.  They are not
-- a coordination-cost function, importance score, speaking-time measure or
-- exhaustive participation count for the meeting.
------------------------------------------------------------------------

observedIssueDegree : Issue → Nat
observedIssueDegree spokesCouncilProposal = 1
observedIssueDegree financeIntegration = 3
observedIssueDegree libraryBudget = 1
observedIssueDegree silentReadingTechnology = 3
observedIssueDegree electricityGenerator = 2
observedIssueDegree townPlanningShelter = 3
observedIssueDegree guestSpeakerCoordination = 2
observedIssueDegree zinesAndPamphlets = 2
observedIssueDegree printedGovernanceArchive = 1
observedIssueDegree meetingTime = 0
observedIssueDegree libraryClosingTime = 0

observedParticipantDegree : Participant → Nat
observedParticipantDegree adash = 1
observedParticipantDegree steve = 3
observedParticipantDegree betsy = 2
observedParticipantDegree stephen = 2
observedParticipantDegree frances = 3
observedParticipantDegree eric = 1
observedParticipantDegree orion = 1
observedParticipantDegree sean = 1
observedParticipantDegree thaddeus = 2
observedParticipantDegree michael = 1
observedParticipantDegree zach = 1

issueDegreeTotal :
  observedIssueDegree spokesCouncilProposal
  + observedIssueDegree financeIntegration
  + observedIssueDegree libraryBudget
  + observedIssueDegree silentReadingTechnology
  + observedIssueDegree electricityGenerator
  + observedIssueDegree townPlanningShelter
  + observedIssueDegree guestSpeakerCoordination
  + observedIssueDegree zinesAndPamphlets
  + observedIssueDegree printedGovernanceArchive
  + observedIssueDegree meetingTime
  + observedIssueDegree libraryClosingTime
  ≡ 18
issueDegreeTotal = refl

------------------------------------------------------------------------
-- Decision/outcome observations are deliberately separate from speaker edges.
-- These constructors state only that the inspected minutes report the named
-- outcome for the issue; they do not assign that outcome as every speaker's
-- individual stance.
------------------------------------------------------------------------

data DecisionObserved : Issue → Set where
  financeConsensus : DecisionObserved financeIntegration
  generatorPriorityConsensus : DecisionObserved electricityGenerator
  printedArchivePositiveConsensus : DecisionObserved printedGovernanceArchive
  meetingTimeConsensus : DecisionObserved meetingTime
  closingTimeNoFixedClosureConsensus : DecisionObserved libraryClosingTime

------------------------------------------------------------------------
-- Source anchors for the bounded specimen.
------------------------------------------------------------------------

meetingDate : String
meetingDate = "2011-10-22"

sourceURL : String
sourceURL =
  "https://peopleslibrary.wordpress.com/2011/10/22/library-working-group-meeting-minutes/"

sourceScope : String
sourceScope =
  "People's Library / OWS Library Working Group meeting; not the whole NYCGA"

------------------------------------------------------------------------
-- No-promotion firewall.
------------------------------------------------------------------------

record LibraryArchivalIncidenceBoundary : Set where
  constructor libraryArchivalIncidenceBoundary
  field
    rowsAreSourceExplicitNamedInteractions : Bool
    outcomesKeptSeparateFromSpeakerRows : Bool
    descriptiveDegreesDerivedFromAdmittedRows : Bool

    attendanceCrossProductPromoted : Bool
    speakerEdgeEncodesAgreement : Bool
    speakerEdgeEncodesVote : Bool
    speakerEdgeEncodesRepresentation : Bool
    speakerEdgeCreatesMandate : Bool
    meetingGraphGeneralisedToAllOWS : Bool
    finiteGraphIsCompleteMeetingTranscript : Bool
    observedDegreeInterpretedAsCoordinationCost : Bool
    finiteGraphPaysCoordinationCostLaw : Bool

open LibraryArchivalIncidenceBoundary public

canonicalLibraryIncidenceBoundary : LibraryArchivalIncidenceBoundary
canonicalLibraryIncidenceBoundary =
  libraryArchivalIncidenceBoundary
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

canonicalOccupyLibraryArchivalIncidenceReceipt : GenericReceipt.GenericReceipt
canonicalOccupyLibraryArchivalIncidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "real bounded OWS Library Working Group incidence graph"
    "DASHI.Governance.OccupyLibraryArchivalIncidenceFiniteExampleExact"
    "canonicalLibraryIncidenceBoundary"
    "instantiates eighteen explicit named participant-to-issue interactions from the 22 October 2011 People's Library working-group minutes, keeps reported consensus outcomes separate, and exposes exact descriptive issue/participant degrees for the admitted edge set"
    "the graph does not infer attendee-by-agenda edges, individual agreement or votes, representation, mandate, movement-wide completeness, or reinterpret descriptive incidence degree as coordination cost"
    "agda -i . DASHI/Governance/OccupyLibraryArchivalIncidenceFiniteExampleRegression.agda"
