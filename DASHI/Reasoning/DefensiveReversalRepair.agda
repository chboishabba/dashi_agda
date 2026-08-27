module DASHI.Reasoning.DefensiveReversalRepair where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.RelationalStateCore as Core
import DASHI.Reasoning.RelationalSharedStateUpdate as Shared

------------------------------------------------------------------------
-- Conflict reconstruction preserves causal order without presuming motive.
------------------------------------------------------------------------

data ConflictRole : Set where
  actorRole affectedRole objectorRole responderRole mediatorRole : ConflictRole

data DefensiveRoute : Set where
  reflectiveRoute egoDefensiveRoute mixedRoute undeterminedRoute : DefensiveRoute

data DARVOPhase : Set where
  noDARVOPhase denyPhase attackPhase reverseRolesPhase : DARVOPhase

data EvidenceStrength : Set where
  stipulatedDefinition logicalConsequence mechanisticHypothesis : EvidenceStrength
  repeatedPatternEvidence quasiCausalEvidence establishedCausalEvidence : EvidenceStrength

record RelationalMisconduct : Set where
  constructor relationalMisconduct
  field
    actor affected : Core.Participant
    observableAct : String
    relationalContext : String
    reportedEffect : String
    evidenceStrength : EvidenceStrength
    misconductReceipt : String

open RelationalMisconduct public

record Complaint : Set where
  constructor complaint
  field
    complainant : Core.Participant
    complainedOf : RelationalMisconduct
    complaintLabel : String
    complaintReceipt : String

record EgoThreatTransition : Set where
  constructor egoThreatTransition
  field
    complaintUnderReview : Complaint
    preferredSelfDescription : List String
    reflectiveExaminationAvailable : Bool
    defensiveDisplacementObserved : Bool
    selectedRoute : DefensiveRoute
    transitionReceipt : String

record DefensiveReflection : Set where
  constructor defensiveReflection
  field
    originalComplaint : Complaint
    reflectedAllegation : Shared.BehaviouralAllegation
    originalComplaintResolvedFirst : Bool
    independentParticularPresent : Bool
    reflectionReceipt : String

record ResolutionAttempt : Set where
  constructor resolutionAttempt
  field
    requester : Core.Participant
    requestForExactAct : Bool
    requestForAgreementHistory : Bool
    requestToRestoreOriginalIssue : Bool
    requestForChangedExpectation : Bool
    attemptReframedAsMisconduct : Bool
    attemptReceipt : String

record CausalConflictPath : Set where
  constructor causalConflictPath
  field
    initiatingAct : String
    primaryImpact : String
    objection : String
    secondaryDistress : String
    counterAllegation : String
    resolutionAttemptDescription : String
    originalIssueStillOpen : Bool
    pathReceipt : String

record DARVOLikePattern : Set where
  constructor darvoLikePattern
  field
    path : CausalConflictPath
    denyOrEvade : Bool
    attackObjector : Bool
    reverseVictimAndOffender : Bool
    deliberateStrategyEstablished : Bool
    patternReceipt : String

record ConflictExpansion : Set where
  constructor conflictExpansion
  field
    originalIssue : String
    generatedCounterIssues : List String
    originalRepairProbabilityReduced : Bool
    eachClarificationCreatesNewAllegation : Bool
    expansionReceipt : String

record DoubleBind : Set where
  constructor doubleBind
  field
    availableResponses : List String
    everyResponsePenalised : Bool
    acceptedRepairRouteExists : Bool
    protectiveWithdrawalPredictable : Bool
    doubleBindReceipt : String

record RepairSequence : Set where
  field
    reconstructWhatPrecededObjection : Bool
    identifyConcreteAct : Bool
    recordPrimaryImpact : Bool
    reviewDeliverySeparately : Bool
    particulariseCounterAllegation : Bool
    testWhetherOriginalIssueWasDisplaced : Bool
    specifyChangeForEachParty : Bool
    preserveBothQuestions : Bool

canonicalRepairSequence : RepairSequence
canonicalRepairSequence = record
  { reconstructWhatPrecededObjection = true
  ; identifyConcreteAct = true
  ; recordPrimaryImpact = true
  ; reviewDeliverySeparately = true
  ; particulariseCounterAllegation = true
  ; testWhetherOriginalIssueWasDisplaced = true
  ; specifyChangeForEachParty = true
  ; preserveBothQuestions = true
  }

record DefensiveReversalAuthorityBoundary : Set where
  field
    distressProvesPriorMisconduct : Bool
    objectionProvesAggression : Bool
    defensivePatternProvesOriginalAllegation : Bool
    darvoLabelAppliedWithoutIncidentReconstruction : Bool
    originalActErasedByDeliveryCritique : Bool
    boundaryNote : String

canonicalDefensiveReversalAuthorityBoundary :
  DefensiveReversalAuthorityBoundary
canonicalDefensiveReversalAuthorityBoundary = record
  { distressProvesPriorMisconduct = false
  ; objectionProvesAggression = false
  ; defensivePatternProvesOriginalAllegation = false
  ; darvoLabelAppliedWithoutIncidentReconstruction = false
  ; originalActErasedByDeliveryCritique = false
  ; boundaryNote =
      "The model preserves act-impact-objection-response order and permits scrutiny of delivery without allowing the secondary dispute to erase the initiating event."
  }
