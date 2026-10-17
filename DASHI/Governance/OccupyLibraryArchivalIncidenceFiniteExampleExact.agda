module DASHI.Governance.OccupyLibraryArchivalIncidenceFiniteExampleExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyParticipantPseudonymisationExact as Privacy

------------------------------------------------------------------------
-- REAL BOUNDED FINITE INCIDENCE EXAMPLE, PSEUDONYMISED.
--
-- Primary archival source:
-- People's Library / Occupy Wall Street Library Working Group minutes,
-- 22 October 2011.
-- https://peopleslibrary.wordpress.com/2011/10/22/library-working-group-meeting-minutes/
--
-- Participant labels in this derived formal table are keyed-HMAC pseudonyms.
-- Raw source names are intentionally not propagated here.
------------------------------------------------------------------------

data Participant : Set where
  p-ebddda : Participant
  p-442ac6 : Participant
  p-aeedd2 : Participant
  p-81d19f : Participant
  p-33f894 : Participant
  p-2b47b2 : Participant
  p-61309c : Participant
  p-a936c6 : Participant
  p-b64222 : Participant
  p-bc1911 : Participant
  p-fc55c2 : Participant

data Issue : Set where
  spokesCouncilProposal financeIntegration libraryBudget silentReadingTechnology electricityGenerator townPlanningShelter guestSpeakerCoordination zinesAndPamphlets printedGovernanceArchive meetingTime libraryClosingTime : Issue

data ExplicitInteraction : Participant → Issue → Set where
  e01 : ExplicitInteraction p-ebddda spokesCouncilProposal
  e02 : ExplicitInteraction p-442ac6 financeIntegration
  e03 : ExplicitInteraction p-aeedd2 financeIntegration
  e04 : ExplicitInteraction p-81d19f libraryBudget
  e05 : ExplicitInteraction p-33f894 financeIntegration
  e06 : ExplicitInteraction p-2b47b2 silentReadingTechnology
  e07 : ExplicitInteraction p-81d19f silentReadingTechnology
  e08 : ExplicitInteraction p-aeedd2 silentReadingTechnology
  e09 : ExplicitInteraction p-61309c electricityGenerator
  e10 : ExplicitInteraction p-33f894 electricityGenerator
  e11 : ExplicitInteraction p-33f894 townPlanningShelter
  e12 : ExplicitInteraction p-a936c6 townPlanningShelter
  e13 : ExplicitInteraction p-b64222 townPlanningShelter
  e14 : ExplicitInteraction p-442ac6 guestSpeakerCoordination
  e15 : ExplicitInteraction p-bc1911 guestSpeakerCoordination
  e16 : ExplicitInteraction p-b64222 zinesAndPamphlets
  e17 : ExplicitInteraction p-fc55c2 zinesAndPamphlets
  e18 : ExplicitInteraction p-442ac6 printedGovernanceArchive

record ObservedEdge : Set where
  constructor observedEdge
  field
    participant : Participant
    issue : Issue
    witness : ExplicitInteraction participant issue
open ObservedEdge public

canonicalObservedEdges : List ObservedEdge
canonicalObservedEdges =
  observedEdge p-ebddda spokesCouncilProposal e01
  ∷ observedEdge p-442ac6 financeIntegration e02
  ∷ observedEdge p-aeedd2 financeIntegration e03
  ∷ observedEdge p-81d19f libraryBudget e04
  ∷ observedEdge p-33f894 financeIntegration e05
  ∷ observedEdge p-2b47b2 silentReadingTechnology e06
  ∷ observedEdge p-81d19f silentReadingTechnology e07
  ∷ observedEdge p-aeedd2 silentReadingTechnology e08
  ∷ observedEdge p-61309c electricityGenerator e09
  ∷ observedEdge p-33f894 electricityGenerator e10
  ∷ observedEdge p-33f894 townPlanningShelter e11
  ∷ observedEdge p-a936c6 townPlanningShelter e12
  ∷ observedEdge p-b64222 townPlanningShelter e13
  ∷ observedEdge p-442ac6 guestSpeakerCoordination e14
  ∷ observedEdge p-bc1911 guestSpeakerCoordination e15
  ∷ observedEdge p-b64222 zinesAndPamphlets e16
  ∷ observedEdge p-fc55c2 zinesAndPamphlets e17
  ∷ observedEdge p-442ac6 printedGovernanceArchive e18
  ∷ []

edgeCount : List ObservedEdge → Nat
edgeCount [] = 0
edgeCount (_ ∷ rest) = suc (edgeCount rest)

canonicalObservedEdgeCount : edgeCount canonicalObservedEdges ≡ 18
canonicalObservedEdgeCount = refl

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
observedParticipantDegree p-ebddda = 1
observedParticipantDegree p-442ac6 = 3
observedParticipantDegree p-aeedd2 = 2
observedParticipantDegree p-81d19f = 2
observedParticipantDegree p-33f894 = 3
observedParticipantDegree p-2b47b2 = 1
observedParticipantDegree p-61309c = 1
observedParticipantDegree p-a936c6 = 1
observedParticipantDegree p-b64222 = 2
observedParticipantDegree p-bc1911 = 1
observedParticipantDegree p-fc55c2 = 1

issueDegreeTotal :
  observedIssueDegree spokesCouncilProposal + observedIssueDegree financeIntegration + observedIssueDegree libraryBudget + observedIssueDegree silentReadingTechnology + observedIssueDegree electricityGenerator + observedIssueDegree townPlanningShelter + observedIssueDegree guestSpeakerCoordination + observedIssueDegree zinesAndPamphlets + observedIssueDegree printedGovernanceArchive + observedIssueDegree meetingTime + observedIssueDegree libraryClosingTime ≡ 18
issueDegreeTotal = refl

data DecisionObserved : Issue → Set where
  financeConsensus : DecisionObserved financeIntegration
  generatorPriorityConsensus : DecisionObserved electricityGenerator
  printedArchivePositiveConsensus : DecisionObserved printedGovernanceArchive
  meetingTimeConsensus : DecisionObserved meetingTime
  closingTimeNoFixedClosureConsensus : DecisionObserved libraryClosingTime

meetingDate : String
meetingDate = "2011-10-22"
sourceURL : String
sourceURL = "https://peopleslibrary.wordpress.com/2011/10/22/library-working-group-meeting-minutes/"
sourceScope : String
sourceScope = "People's Library / OWS Library Working Group meeting; not the whole NYCGA"

record LibraryArchivalIncidenceBoundary : Set where
  constructor libraryArchivalIncidenceBoundary
  field
    rowsAreSourceExplicitPseudonymousInteractions outcomesKeptSeparateFromSpeakerRows descriptiveDegreesDerivedFromAdmittedRows rawNamesPropagatedIntoFormalTable attendanceCrossProductPromoted speakerEdgeEncodesAgreement speakerEdgeEncodesVote speakerEdgeEncodesRepresentation speakerEdgeCreatesMandate meetingGraphGeneralisedToAllOWS finiteGraphIsCompleteMeetingTranscript observedDegreeInterpretedAsCoordinationCost finiteGraphPaysCoordinationCostLaw : Bool
open LibraryArchivalIncidenceBoundary public

canonicalLibraryIncidenceBoundary : LibraryArchivalIncidenceBoundary
canonicalLibraryIncidenceBoundary =
  libraryArchivalIncidenceBoundary true true true false false false false false false false false false false

canonicalOccupyLibraryArchivalIncidenceReceipt : GenericReceipt.GenericReceipt
canonicalOccupyLibraryArchivalIncidenceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "pseudonymised bounded OWS Library Working Group incidence graph"
    "DASHI.Governance.OccupyLibraryArchivalIncidenceFiniteExampleExact"
    "canonicalLibraryIncidenceBoundary"
    "instantiates eighteen explicit participant-to-issue interactions from the 22 October 2011 People's Library working-group minutes using collision-audited opaque participant tokens and keeping reported consensus outcomes separate"
    "raw names are not propagated into this derived table; source citation remains public, pseudonym tokens preserve bounded correlation only, and the graph does not infer votes, representation, mandate, completeness or coordination cost"
    "agda -i . DASHI/Governance/OccupyLibraryArchivalIncidenceFiniteExampleRegression.agda"
