module DASHI.Cognition.PNF.SensibLawViolationPrerequisiteMeetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawLiveProducerCoordinateEvidenceBridgeExact as Bridge
import DASHI.Cognition.PNF.SensibLawResolvedLegalEvidenceExact as Evidence
import DASHI.Cognition.PNF.SensibLawParticipantLegalRoleWrongTypeBidiExact as LegalRole

------------------------------------------------------------------------
-- WRONGTYPE APPLICABILITY RECEIPT IN STATE
------------------------------------------------------------------------

record WrongTypeApplicabilityReceiptInState
    (state : Status.SemanticCommitmentState) : Set where
  constructor wrongTypeApplicabilityReceiptInState
  field
    receipt : Legal.WrongTypeApplicabilityReceipt
    legalStatusMembership : Legal.legalStatus receipt Bridge.∈ Status.legalStatuses state
    applicabilityResolution : Status.ApplicabilityResolutionReceipt
    sameLegalStatus :
      Status.legalStatus applicabilityResolution ≡ Legal.legalStatus receipt
    sameApplicability :
      Status.resultingApplicability applicabilityResolution
      ≡ Legal.resultingApplicability receipt
    receiptReference : String

open WrongTypeApplicabilityReceiptInState public

------------------------------------------------------------------------
-- Every element evaluation must belong to the exact WrongType under review.
------------------------------------------------------------------------

data EvaluationsForWrongType
    (wrong : Ontology.StableId) : List Legal.WrongElementEvaluation → Set where
  noEvaluations : EvaluationsForWrongType wrong []
  evaluationFor :
    ∀ {evaluation rest} →
    Legal.wrongTypeReference evaluation ≡ wrong →
    EvaluationsForWrongType wrong rest →
    EvaluationsForWrongType wrong (evaluation ∷ rest)

record ViolationDecision
    (evaluations : List Legal.WrongElementEvaluation) : Set where
  constructor violationDecision
  field
    resultingViolation : Status.ViolationStatus
    decisionEvidenceReferences : List String
    resolverReference : String
    evaluationsActuallyConsidered : Bool
    evaluationsActuallyConsideredIsTrue : evaluationsActuallyConsidered ≡ true

open ViolationDecision public

record ViolationPrerequisiteBundle
    (state : Status.SemanticCommitmentState) : Set where
  constructor violationPrerequisiteBundle
  field
    applicability : WrongTypeApplicabilityReceiptInState state
    legalRole : Bridge.LegalRoleReceiptInState state
    resolvedEvidence : Evidence.ResolvedLegalEvidenceReceiptInState state
    sameWrongTypeAsLegalRole :
      LegalRole.wrongType (Bridge.weld legalRole)
      ≡ Legal.wrongType (receipt applicability)
    sameEventAsLegalRole :
      Ontology.Event.eventId (LegalRole.event (Bridge.weld legalRole))
      ≡ Ontology.Event.eventId (Legal.event (receipt applicability))
    sameEvidenceEvent :
      Ontology.stableId (Status.eventReference (Evidence.eventStatus resolvedEvidence))
      ≡ Ontology.Event.eventId (Legal.event (receipt applicability))
    bundleReference : String

open ViolationPrerequisiteBundle public

record ViolationMeetInput
    (state : Status.SemanticCommitmentState) : Set where
  constructor violationMeetInput
  field
    prerequisites : ViolationPrerequisiteBundle state
    elementEvaluations : List Legal.WrongElementEvaluation
    evaluationsMatchWrongType :
      EvaluationsForWrongType
        (Ontology.WrongType.wrongTypeId
          (Legal.wrongType (receipt (applicability prerequisites))))
        elementEvaluations
    decision : ViolationDecision elementEvaluations

open ViolationMeetInput public

compileViolationMeet :
  ∀ {state} → ViolationMeetInput state → Legal.ViolationReceipt
compileViolationMeet input =
  Legal.violationReceipt
    (receipt (applicability (prerequisites input)))
    (elementEvaluations input)
    (resultingViolation (decision input))
    refl
    (resolverReference (decision input))

compiledViolationMatchesDecision :
  ∀ {state} (input : ViolationMeetInput state) →
  Legal.resultingViolation (compileViolationMeet input)
  ≡ resultingViolation (decision input)
compiledViolationMatchesDecision input = refl

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data ApplicabilityAutomaticallyProvesViolation : Set where
data ElementEvaluationForOtherWrongTypeMayBeBorrowed : Set where
data LegalRoleAloneProvesViolation : Set where
data ResolvedEvidenceAloneProvesViolation : Set where
data ViolationAutomaticallyProvesLiability : Set where

applicabilityDoesNotAutomaticallyProveViolation :
  ApplicabilityAutomaticallyProvesViolation → ⊥
applicabilityDoesNotAutomaticallyProveViolation ()

otherWrongTypeEvaluationCannotBeBorrowed :
  ElementEvaluationForOtherWrongTypeMayBeBorrowed → ⊥
otherWrongTypeEvaluationCannotBeBorrowed ()

legalRoleAloneDoesNotProveViolation : LegalRoleAloneProvesViolation → ⊥
legalRoleAloneDoesNotProveViolation ()

resolvedEvidenceAloneDoesNotProveViolation : ResolvedEvidenceAloneProvesViolation → ⊥
resolvedEvidenceAloneDoesNotProveViolation ()

violationDoesNotAutomaticallyProveLiability : ViolationAutomaticallyProvesLiability → ⊥
violationDoesNotAutomaticallyProveLiability ()

record ViolationPrerequisiteMeetBoundary : Set where
  constructor violation-prerequisite-meet-boundary
  field
    paidApplicabilityRequired : Bool
    sameWrongTypeLegalRoleRequired : Bool
    sameEventLegalRoleRequired : Bool
    sameEventEvidenceRequired : Bool
    elementEvaluationsWrongTypeIndexed : Bool
    explicitViolationDecisionRequired : Bool
    applicabilityAloneProvesViolation : Bool
    violationAutomaticallyProvesLiability : Bool

canonicalViolationPrerequisiteMeetBoundary : ViolationPrerequisiteMeetBoundary
canonicalViolationPrerequisiteMeetBoundary =
  violation-prerequisite-meet-boundary true true true true true true false false
