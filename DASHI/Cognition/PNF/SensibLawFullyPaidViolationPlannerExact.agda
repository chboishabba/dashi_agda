module DASHI.Cognition.PNF.SensibLawFullyPaidViolationPlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawFullyPaidApplicabilityFixtureExact as Paid
import DASHI.Cognition.PNF.SensibLawParticipantLegalRoleLiveBidiExact as LegalRoleLive
import DASHI.Cognition.PNF.SensibLawViolationPrerequisiteMeetExact as ViolationMeet
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal
import DASHI.Cognition.PNF.SensibLawLiveProducerCoordinateEvidenceBridgeExact as Bridge
import DASHI.Cognition.PNF.SensibLawResolvedLegalEvidenceExact as Evidence
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as Authority
import DASHI.Cognition.PNF.SensibLawLegalJurisdictionEvidenceExact as Jurisdiction
import DASHI.Cognition.PNF.SensibLawActiveRequirementExecutionPlannerExact as Planner
import DASHI.Cognition.PNF.SensibLawRequirementProducerRoutingExact as Routing

------------------------------------------------------------------------
-- The already-paid applicability receipt is the input currency for violation.
------------------------------------------------------------------------

applicabilityInPaidState :
  ViolationMeet.WrongTypeApplicabilityReceiptInState Paid.fixtureState
applicabilityInPaidState =
  ViolationMeet.wrongTypeApplicabilityReceiptInState
    Paid.compiledApplicability
    Bridge.here
    Paid.applicabilityResolution
    refl
    refl
    "fully-paid applicability receipt before violation evaluation"

violationPrerequisites :
  ViolationMeet.ViolationPrerequisiteBundle Paid.fixtureState
violationPrerequisites =
  ViolationMeet.violationPrerequisiteBundle
    applicabilityInPaidState
    Paid.ownedLegalRole
    Paid.resolvedEvidence
    refl
    refl
    refl
    "same WrongType/event legal-role/evidence bundle"

fixtureElementEvaluation : Legal.WrongElementEvaluation
fixtureElementEvaluation =
  Legal.wrongElementEvaluation
    (Ontology.WrongType.wrongTypeId LegalRoleLive.fixtureWrongType)
    "element:fixture:dog-walk-duty"
    Legal.elementSatisfied
    ("fixture documentary evidence" ∷ [])
    "fixture wrong-element evaluator"

fixtureEvaluations : List Legal.WrongElementEvaluation
fixtureEvaluations = fixtureElementEvaluation ∷ []

evaluationsMatchWrongType :
  ViolationMeet.EvaluationsForWrongType
    (Ontology.WrongType.wrongTypeId LegalRoleLive.fixtureWrongType)
    fixtureEvaluations
evaluationsMatchWrongType =
  ViolationMeet.evaluationFor refl ViolationMeet.noEvaluations

violationDecision : ViolationMeet.ViolationDecision fixtureEvaluations
violationDecision =
  ViolationMeet.violationDecision
    Status.violationCandidate
    ("fixture element satisfied; applicability remains candidate" ∷ [])
    "fixture violation decision policy"
    true refl

violationInput : ViolationMeet.ViolationMeetInput Paid.fixtureState
violationInput =
  ViolationMeet.violationMeetInput
    violationPrerequisites
    fixtureEvaluations
    evaluationsMatchWrongType
    violationDecision

compiledViolation : Legal.ViolationReceipt
compiledViolation = ViolationMeet.compileViolationMeet violationInput

compiledViolationIsCandidate :
  Legal.resultingViolation compiledViolation ≡ Status.violationCandidate
compiledViolationIsCandidate = refl

------------------------------------------------------------------------
-- Append a post-violation legal-status snapshot rather than rewriting history.
------------------------------------------------------------------------

postViolationLegalStatus : Status.LegalStatusProduct
postViolationLegalStatus =
  Status.legalStatusProduct
    Status.legalSystemJurisdiction
    Status.legalAuthority
    Status.conditionUnresolved
    Status.applicabilityCandidate
    Status.violationCandidate
    Status.liabilityUnresolved
    Status.burdenKindUnresolved
    Status.standardUnresolved
    Status.submission
    Status.normativeRelationUnresolved

postViolationState : Status.SemanticCommitmentState
postViolationState =
  Status.semanticCommitmentState
    (Status.sourceCandidate Paid.fixtureState)
    (Status.subjects Paid.fixtureState)
    (Status.events Paid.fixtureState)
    (Status.propositions Paid.fixtureState)
    (postViolationLegalStatus ∷ Status.legalStatuses Paid.fixtureState)
    (Status.candidateOnly Paid.fixtureState)
    (Status.governedAdmissionPresent Paid.fixtureState)

ownedViolation : Bridge.ViolationReceiptInState postViolationState
ownedViolation =
  Bridge.violationReceiptInState
    compiledViolation
    postViolationLegalStatus
    Bridge.here
    refl
    refl
    "compiled violation retained as post-violation legal-status snapshot"

------------------------------------------------------------------------
-- Transport previously-paid receipts into the refined state.
------------------------------------------------------------------------

ownedApplicability : Bridge.ApplicabilityReceiptInState postViolationState
ownedApplicability =
  Bridge.applicabilityReceiptInState
    Paid.applicabilityResolution
    (Bridge.there Bridge.here)
    "prior applicability snapshot retained after violation refinement"

ownedLegalRole : Bridge.LegalRoleReceiptInState postViolationState
ownedLegalRole =
  Bridge.legalRoleReceiptInState
    LegalRoleLive.fixtureDutyBearerWeld
    Bridge.here
    Paid.fixtureEvent
    Bridge.here
    refl
    "same duty-bearer weld retained after violation refinement"

resolvedEvidence : Evidence.ResolvedLegalEvidenceReceiptInState postViolationState
resolvedEvidence =
  Evidence.resolvedLegalEvidenceReceiptInState
    Paid.fixtureEvidenceItem
    Paid.fixtureEvidenceLink
    Paid.fixtureEvent
    Paid.fixtureProposition
    Bridge.here
    Bridge.here
    refl refl
    Evidence.documentaryEvidenceLegalUse
    true refl
    ("provenance:fixture:dog-walk-document" ∷ [])
    "same resolved evidence retained after violation refinement"

authorityReceipt : Authority.LegalSourceAuthorityReceiptInState postViolationState
authorityReceipt =
  Authority.legalSourceAuthorityReceiptInState
    Paid.fixtureSource
    Paid.fixtureSystem
    refl
    Paid.fixtureLegalStatus
    (Bridge.there Bridge.here)
    refl
    Authority.validityCurrent
    Authority.currentValidity
    ("Fixture Dog Duty Act s 1" ∷ [])
    ("fixture validity interval checked" ∷ [])
    ("fixture source recognized as legal authority" ∷ [])
    "same authority retained after violation refinement"

jurisdictionReceipt : Jurisdiction.LegalJurisdictionReceiptInState postViolationState
jurisdictionReceipt =
  Jurisdiction.legalJurisdictionReceiptInState
    Paid.fixtureCase
    Paid.fixtureSystem
    refl
    Paid.fixtureLegalStatus
    (Bridge.there Bridge.here)
    Jurisdiction.legalSystemResolved
    ("fixture case legal-system identity" ∷ [])
    ("fixture legal system record" ∷ [])
    "same jurisdiction retained after violation refinement"

------------------------------------------------------------------------
-- Liability query now has every declared prerequisite paid.
------------------------------------------------------------------------

applicabilityEvidence =
  Bridge.applicabilityReceiptPaysActiveCoordinate refl ownedApplicability
violationEvidence =
  Bridge.violationReceiptPaysActiveCoordinate refl ownedViolation
legalRoleEvidence =
  Bridge.legalRoleReceiptPaysActiveCoordinate refl ownedLegalRole
resolvedEvidenceEvidence =
  Evidence.resolvedLegalEvidencePaysActiveCoordinate refl resolvedEvidence
authorityEvidence =
  Authority.legalSourceAuthorityPaysActiveCoordinate refl authorityReceipt
jurisdictionEvidence =
  Jurisdiction.legalJurisdictionPaysActiveCoordinate refl jurisdictionReceipt

applicabilityPlan =
  Planner.planRequirement applicabilityEvidence "reuse applicability after violation"
violationPlan =
  Planner.planRequirement violationEvidence "reuse compiled violation"
legalRolePlan =
  Planner.planRequirement legalRoleEvidence "reuse resolved legal role"
resolvedEvidencePlan =
  Planner.planRequirement resolvedEvidenceEvidence "reuse resolved legal evidence"
authorityPlan =
  Planner.planRequirement authorityEvidence "reuse legal-source authority"
jurisdictionPlan =
  Planner.planRequirement jurisdictionEvidence "reuse resolved jurisdiction"

applicabilityReuses : Planner.action applicabilityPlan ≡ Planner.reuseExisting
applicabilityReuses = refl
violationReuses : Planner.action violationPlan ≡ Planner.reuseExisting
violationReuses = refl
legalRoleReuses : Planner.action legalRolePlan ≡ Planner.reuseExisting
legalRoleReuses = refl
resolvedEvidenceReuses : Planner.action resolvedEvidencePlan ≡ Planner.reuseExisting
resolvedEvidenceReuses = refl
authorityReuses : Planner.action authorityPlan ≡ Planner.reuseExisting
authorityReuses = refl
jurisdictionReuses : Planner.action jurisdictionPlan ≡ Planner.reuseExisting
jurisdictionReuses = refl

applicabilityWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid applicability"
violationWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid violation"
legalRoleWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid legal role"
resolvedEvidenceWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid legal evidence"
authorityWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid legal authority"
jurisdictionWork = Routing.routedWork Routing.noProducerInvocation refl Routing.reuseWithoutProducer "paid jurisdiction"

------------------------------------------------------------------------
-- Paying the liability prerequisites still does not itself create liability.
------------------------------------------------------------------------

data PaidLiabilityPrerequisitesAutomaticallyCreateLiability : Set where
data ViolationCandidateAutomaticallyBecomesViolationAdmitted : Set where
data PostViolationStateErasesPriorApplicabilitySnapshot : Set where

paidLiabilityPrerequisitesDoNotCreateLiability :
  PaidLiabilityPrerequisitesAutomaticallyCreateLiability → ⊥
paidLiabilityPrerequisitesDoNotCreateLiability ()

violationCandidateDoesNotAutoAdmitViolation :
  ViolationCandidateAutomaticallyBecomesViolationAdmitted → ⊥
violationCandidateDoesNotAutoAdmitViolation ()

postViolationStateRetainsPriorApplicability :
  PostViolationStateErasesPriorApplicabilitySnapshot → ⊥
postViolationStateRetainsPriorApplicability ()

record FullyPaidViolationPlannerBoundary : Set where
  constructor fully-paid-violation-planner-boundary
  field
    applicabilityReceiptReused : Bool
    sameWrongTypeRoleRequired : Bool
    sameEventEvidenceRequired : Bool
    wrongElementsIndexedToWrongType : Bool
    explicitViolationDecisionRequired : Bool
    postViolationStateRetainsPriorSnapshot : Bool
    liabilityApplicabilityReuses : Bool
    liabilityViolationReuses : Bool
    liabilityLegalRoleReuses : Bool
    liabilityEvidenceReuses : Bool
    liabilityAuthorityReuses : Bool
    liabilityJurisdictionReuses : Bool
    paidPrerequisitesAutomaticallyCreateLiability : Bool

canonicalFullyPaidViolationPlannerBoundary : FullyPaidViolationPlannerBoundary
canonicalFullyPaidViolationPlannerBoundary =
  fully-paid-violation-planner-boundary
    true true true true true true true true true true true true false
