module DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Interop.SensibLawOntologyTopology as Ontology

------------------------------------------------------------------------
-- BIDI CAMPAIGN 6: WrongType applicability -> violation -> liability -> burden
-- -> remedy eligibility.  Existing WrongType is the legal ontology owner.
-- Each downstream conclusion consumes the previous receipt but is not implied
-- by it definitionally.
------------------------------------------------------------------------

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

------------------------------------------------------------------------
-- Semantic input gate.
--
-- A legal engine may reason ABOUT an allegation, denial, assertion or
-- hypothetical without pretending that the underlying event occurred.  Those
-- discourse states therefore enter only candidate applicability here.
-- Admitted applicability requires an explicit established-occurrence route.
-- A court finding may be legally usable while universal truth remains unresolved.
------------------------------------------------------------------------

data LegalEventUse :
    Status.OccurrenceStatus →
    Status.PropositionStatus →
    Status.TruthStatus →
    Status.ApplicabilityStatus → Set where

  allegationCandidateUse :
    LegalEventUse
      Status.allegedOccurrence
      Status.allegedProposition
      Status.truthUnresolved
      Status.applicabilityCandidate

  assertionCandidateUse :
    LegalEventUse
      Status.assertedOccurrence
      Status.assertedBySource
      Status.truthUnresolved
      Status.applicabilityCandidate

  denialCandidateUse :
    LegalEventUse
      Status.deniedOccurrence
      Status.deniedProposition
      Status.truthUnresolved
      Status.applicabilityCandidate

  reportedCandidateUse :
    LegalEventUse
      Status.reportedOccurrence
      Status.quotedReportedProposition
      Status.truthUnresolved
      Status.applicabilityCandidate

  hypotheticalCandidateUse :
    LegalEventUse
      Status.hypotheticalOccurrence
      Status.hypotheticalProposition
      Status.truthUnresolved
      Status.applicabilityCandidate

  conditionalCandidateUse :
    LegalEventUse
      Status.conditionalOccurrence
      Status.hypotheticalProposition
      Status.truthUnresolved
      Status.applicabilityCandidate

  establishedFindingUse :
    LegalEventUse
      Status.occurrenceAdmitted
      Status.foundAsFact
      Status.truthUnresolved
      Status.applicabilityAdmitted

  governedTruthUse :
    LegalEventUse
      Status.occurrenceAdmitted
      Status.admittedProposition
      Status.truthAdmitted
      Status.applicabilityAdmitted

record SemanticLegalInputGate (event : Ontology.Event) : Set where
  constructor semanticLegalInputGate
  field
    eventStatus : Status.EventStatusProduct
    propositionStatus : Status.PropositionStatusProduct
    sameEventReference :
      Status.eventReference eventStatus
      ≡ Ontology.StableId.value (Ontology.Event.eventId event)
    resultingApplicability : Status.ApplicabilityStatus
    legalEventUse :
      LegalEventUse
        (Status.occurrence eventStatus)
        (Status.propositionStatus propositionStatus)
        (Status.truthStatus propositionStatus)
        resultingApplicability

open SemanticLegalInputGate public

record WrongTypeApplicabilityReceipt : Set where
  constructor wrongTypeApplicabilityReceipt
  field
    event : Ontology.Event
    wrongType : Ontology.WrongType
    interpretation : Ontology.WrongTypeInterpretation
    semanticInput : SemanticLegalInputGate event
    legalStatus : Status.LegalStatusProduct
    sameEvent :
      Ontology.WrongTypeInterpretation.interpretedEvent interpretation
      ≡ Ontology.Event.eventId event
    sameWrongType :
      Ontology.WrongTypeInterpretation.interpretedAs interpretation
      ≡ Ontology.WrongType.wrongTypeId wrongType
    sameSystem :
      Ontology.WrongTypeInterpretation.underSystem interpretation
      ≡ Ontology.WrongType.definingSystem wrongType
    resultingApplicability : Status.ApplicabilityStatus
    applicabilityMatchesSemanticGate :
      resultingApplicability
      ≡ SemanticLegalInputGate.resultingApplicability semanticInput
    typedMeetReference : String
    temporalReference : String
    jurisdictionReference : String
    exceptionReference : String
    authorityReference : String

open WrongTypeApplicabilityReceipt public

data ElementDisposition : Set where
  elementSatisfied elementUnsatisfied elementContested elementUnresolved
  : ElementDisposition

record WrongElementEvaluation : Set where
  constructor wrongElementEvaluation
  field
    wrongTypeReference : Ontology.StableId
    elementReference : String
    disposition : ElementDisposition
    evidenceReferences : List String
    evaluatorReference : String

open WrongElementEvaluation public

record ViolationReceipt : Set where
  constructor violationReceipt
  field
    applicabilityReceipt : WrongTypeApplicabilityReceipt
    elementEvaluations : List WrongElementEvaluation
    resultingViolation : Status.ViolationStatus
    sameWrongTypeReference :
      Ontology.WrongType.wrongTypeId (wrongType applicabilityReceipt)
      ≡ Ontology.WrongType.wrongTypeId (wrongType applicabilityReceipt)
    resolverReference : String

open ViolationReceipt public

record LiabilityReceipt : Set where
  constructor liabilityReceipt
  field
    violationReceipt : ViolationReceipt
    culpability : Ontology.Culpability
    culpabilityMatchesWrongType :
      culpability
      ≡ Ontology.WrongType.culpability
          (wrongType (applicabilityReceipt violationReceipt))
    resultingLiability : Status.LiabilityStatus
    liablePartyReference : String
    evidenceReferences : List String
    resolverReference : String

open LiabilityReceipt public

record BurdenReceipt : Set where
  constructor burdenReceipt
  field
    issueReference : String
    bearerReference : String
    burden : Status.BurdenKind
    standard : Status.StandardOfProof
    propositionReference : String
    sourceReferences : List String
    legalSystemReference : Ontology.StableId
    resolverReference : String

open BurdenReceipt public

record RemedyEligibilityReceipt : Set where
  constructor remedyEligibilityReceipt
  field
    liabilityReceipt : LiabilityReceipt
    remedyReference : Ontology.StableId
    remedyDeclaredForWrongType :
      remedyReference ∈
        Ontology.WrongType.remedyIds
          (wrongType (applicabilityReceipt (violationReceipt liabilityReceipt)))
    protectedInterestReferences : List Ontology.StableId
    harmReferences : List Ontology.StableId
    remedyEligible : Bool
    resolverReference : String

open RemedyEligibilityReceipt public

------------------------------------------------------------------------
-- Reverse/BIDI demand propagation: a downstream consumer can state exactly
-- which upstream receipt is missing without inventing the missing conclusion.
------------------------------------------------------------------------

data LegalConsumerNeed : Set where
  needsSemanticOccurrence needsApplicability needsViolation needsLiability
  needsBurden needsRemedy : LegalConsumerNeed

data RequiredReceiptKind : Set where
  semanticOccurrenceReceiptKind applicabilityReceiptKind violationReceiptKind
  liabilityReceiptKind burdenReceiptKind remedyReceiptKind : RequiredReceiptKind

requiredReceipt : LegalConsumerNeed → RequiredReceiptKind
requiredReceipt needsSemanticOccurrence = semanticOccurrenceReceiptKind
requiredReceipt needsApplicability = applicabilityReceiptKind
requiredReceipt needsViolation = violationReceiptKind
requiredReceipt needsLiability = liabilityReceiptKind
requiredReceipt needsBurden = burdenReceiptKind
requiredReceipt needsRemedy = remedyReceiptKind

------------------------------------------------------------------------
-- Hard no-go laws.
------------------------------------------------------------------------

data AllegationAutomaticallyEstablishedEvent : Set where
data AssertionAutomaticallyEstablishedEvent : Set where
data DenialIsNegatedEventFact : Set where
data WrongTypeInterpretationAutomaticallyApplicable : Set where
data ApplicableAutomaticallyViolated : Set where
data ViolationAutomaticallyLiable : Set where
data LiabilityAutomaticallySelectsRemedy : Set where
data BurdenBearerAutomaticallySyntacticSubject : Set where
data RemedyMembershipProvesEligibility : Set where

allegationDoesNotEstablishEvent : AllegationAutomaticallyEstablishedEvent → ⊥
allegationDoesNotEstablishEvent ()

assertionDoesNotEstablishEvent : AssertionAutomaticallyEstablishedEvent → ⊥
assertionDoesNotEstablishEvent ()

denialDoesNotBecomeNegatedEventFact : DenialIsNegatedEventFact → ⊥
denialDoesNotBecomeNegatedEventFact ()

wrongTypeInterpretationDoesNotAutoApply :
  WrongTypeInterpretationAutomaticallyApplicable → ⊥
wrongTypeInterpretationDoesNotAutoApply ()

applicabilityDoesNotAutoViolate : ApplicableAutomaticallyViolated → ⊥
applicabilityDoesNotAutoViolate ()

violationDoesNotAutoCreateLiability : ViolationAutomaticallyLiable → ⊥
violationDoesNotAutoCreateLiability ()

liabilityDoesNotAutoSelectRemedy : LiabilityAutomaticallySelectsRemedy → ⊥
liabilityDoesNotAutoSelectRemedy ()

burdenBearerNotGrammarSubject : BurdenBearerAutomaticallySyntacticSubject → ⊥
burdenBearerNotGrammarSubject ()

remedyMembershipDoesNotProveEligibility : RemedyMembershipProvesEligibility → ⊥
remedyMembershipDoesNotProveEligibility ()
