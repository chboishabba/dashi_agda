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

record WrongTypeApplicabilityReceipt : Set where
  constructor wrongTypeApplicabilityReceipt
  field
    event : Ontology.Event
    wrongType : Ontology.WrongType
    interpretation : Ontology.WrongTypeInterpretation
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
  needsApplicability needsViolation needsLiability needsBurden needsRemedy
  : LegalConsumerNeed

data RequiredReceiptKind : Set where
  applicabilityReceiptKind violationReceiptKind liabilityReceiptKind
  burdenReceiptKind remedyReceiptKind : RequiredReceiptKind

requiredReceipt : LegalConsumerNeed → RequiredReceiptKind
requiredReceipt needsApplicability = applicabilityReceiptKind
requiredReceipt needsViolation = violationReceiptKind
requiredReceipt needsLiability = liabilityReceiptKind
requiredReceipt needsBurden = burdenReceiptKind
requiredReceipt needsRemedy = remedyReceiptKind

------------------------------------------------------------------------
-- Hard no-go laws.
------------------------------------------------------------------------

data WrongTypeInterpretationAutomaticallyApplicable : Set where
data ApplicableAutomaticallyViolated : Set where
data ViolationAutomaticallyLiable : Set where
data LiabilityAutomaticallySelectsRemedy : Set where
data BurdenBearerAutomaticallySyntacticSubject : Set where
data RemedyMembershipProvesEligibility : Set where

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
