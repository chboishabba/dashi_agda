module DASHI.Cognition.PNF.SensibLawLiabilityPrerequisiteMeetExact where

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
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as Authority
import DASHI.Cognition.PNF.SensibLawLegalJurisdictionEvidenceExact as Jurisdiction
import DASHI.Cognition.PNF.SensibLawParticipantLegalRoleWrongTypeBidiExact as LegalRole

data LegalViolationUse :
    Status.ViolationStatus → Status.LiabilityStatus → Set where
  unresolvedViolationUse :
    LegalViolationUse Status.violationUnresolved Status.liabilityUnresolved
  candidateViolationUse :
    LegalViolationUse Status.violationCandidate Status.liabilityCandidate
  admittedViolationCandidateUse :
    LegalViolationUse Status.violationAdmitted Status.liabilityCandidate
  admittedViolationLiabilityUse :
    LegalViolationUse Status.violationAdmitted Status.liabilityAdmitted
  admittedNoViolationUse :
    LegalViolationUse Status.noViolationAdmitted Status.noLiabilityAdmitted

record LiabilityPrerequisiteBundle
    (state : Status.SemanticCommitmentState) : Set where
  constructor liabilityPrerequisiteBundle
  field
    violation : Bridge.ViolationReceiptInState state
    legalRole : Bridge.LegalRoleReceiptInState state
    resolvedEvidence : Evidence.ResolvedLegalEvidenceReceiptInState state
    legalSourceAuthority : Authority.LegalSourceAuthorityReceiptInState state
    resolvedJurisdiction : Jurisdiction.LegalJurisdictionReceiptInState state
    sameWrongTypeAsLegalRole :
      LegalRole.wrongType (Bridge.weld legalRole)
      ≡ Legal.wrongType
          (Legal.applicabilityReceipt (Bridge.receipt violation))
    sameEventAsLegalRole :
      Ontology.Event.eventId (LegalRole.event (Bridge.weld legalRole))
      ≡ Ontology.Event.eventId
          (Legal.event (Legal.applicabilityReceipt (Bridge.receipt violation)))
    sameEvidenceEvent :
      Ontology.stableId
        (Status.eventReference (Evidence.eventStatus resolvedEvidence))
      ≡ Ontology.Event.eventId
          (Legal.event (Legal.applicabilityReceipt (Bridge.receipt violation)))
    sameAuthorityJurisdictionLegalStatus :
      Authority.legalStatus legalSourceAuthority
      ≡ Jurisdiction.legalStatus resolvedJurisdiction
    sameAuthorityJurisdictionSystem :
      Authority.system legalSourceAuthority
      ≡ Jurisdiction.system resolvedJurisdiction
    sameWrongTypeSystemAsResolvedSystem :
      Ontology.WrongType.definingSystem
        (Legal.wrongType
          (Legal.applicabilityReceipt (Bridge.receipt violation)))
      ≡ Ontology.LegalSystem.systemId
          (Authority.system legalSourceAuthority)
    bundleReference : String

open LiabilityPrerequisiteBundle public

record LiabilityDecision
    {state : Status.SemanticCommitmentState}
    (prerequisites : LiabilityPrerequisiteBundle state) : Set where
  constructor liabilityDecision
  field
    resultingLiability : Status.LiabilityStatus
    legalViolationUse :
      LegalViolationUse
        (Legal.resultingViolation (Bridge.receipt (violation prerequisites)))
        resultingLiability
    liablePartyReference : String
    evidenceReferences : List String
    resolverReference : String
    culpabilityActuallyConsidered : Bool
    culpabilityActuallyConsideredIsTrue : culpabilityActuallyConsidered ≡ true

open LiabilityDecision public

record LiabilityMeetInput
    (state : Status.SemanticCommitmentState) : Set where
  constructor liabilityMeetInput
  field
    prerequisites : LiabilityPrerequisiteBundle state
    culpability : Ontology.Culpability
    culpabilityMatchesWrongType :
      culpability
      ≡ Ontology.WrongType.culpability
          (Legal.wrongType
            (Legal.applicabilityReceipt
              (Bridge.receipt (violation prerequisites))))
    decision : LiabilityDecision prerequisites

open LiabilityMeetInput public

compileLiabilityMeet :
  ∀ {state} → LiabilityMeetInput state → Legal.LiabilityReceipt
compileLiabilityMeet input =
  Legal.liabilityReceipt
    (Bridge.receipt (violation (prerequisites input)))
    (culpability input)
    (culpabilityMatchesWrongType input)
    (resultingLiability (decision input))
    (liablePartyReference (decision input))
    (evidenceReferences (decision input))
    (resolverReference (decision input))

compiledLiabilityMatchesDecision :
  ∀ {state} (input : LiabilityMeetInput state) →
  Legal.resultingLiability (compileLiabilityMeet input)
  ≡ resultingLiability (decision input)
compiledLiabilityMatchesDecision input = refl

data CandidateViolationAdmitsLiability : Set where
data NoViolationAdmittedStillAllowsLiabilityAdmitted : Set where
data ViolationAdmittedAutomaticallyCreatesLiability : Set where
data CulpabilityFromOtherWrongTypeMayBeBorrowed : Set where
data LegalRoleForOtherEventMayBeBorrowed : Set where
data AuthorityOrJurisdictionMayComeFromOtherSystem : Set where
data LiabilityAutomaticallySelectsRemedy : Set where

candidateViolationDoesNotAdmitLiability : CandidateViolationAdmitsLiability → ⊥
candidateViolationDoesNotAdmitLiability ()
noViolationDoesNotAllowAdmittedLiability : NoViolationAdmittedStillAllowsLiabilityAdmitted → ⊥
noViolationDoesNotAllowAdmittedLiability ()
admittedViolationDoesNotAutomaticallyCreateLiability : ViolationAdmittedAutomaticallyCreatesLiability → ⊥
admittedViolationDoesNotAutomaticallyCreateLiability ()
otherWrongTypeCulpabilityCannotBeBorrowed : CulpabilityFromOtherWrongTypeMayBeBorrowed → ⊥
otherWrongTypeCulpabilityCannotBeBorrowed ()
otherEventLegalRoleCannotBeBorrowed : LegalRoleForOtherEventMayBeBorrowed → ⊥
otherEventLegalRoleCannotBeBorrowed ()
otherSystemAuthorityJurisdictionCannotBeBorrowed : AuthorityOrJurisdictionMayComeFromOtherSystem → ⊥
otherSystemAuthorityJurisdictionCannotBeBorrowed ()
liabilityDoesNotAutomaticallySelectRemedy : LiabilityAutomaticallySelectsRemedy → ⊥
liabilityDoesNotAutomaticallySelectRemedy ()

record LiabilityPrerequisiteMeetBoundary : Set where
  constructor liability-prerequisite-meet-boundary
  field
    violationReceiptRequired : Bool
    sameWrongTypeLegalRoleRequired : Bool
    sameEventLegalRoleRequired : Bool
    sameEventEvidenceRequired : Bool
    sameAuthorityJurisdictionStatusRequired : Bool
    sameAuthorityJurisdictionSystemRequired : Bool
    wrongTypeSystemMatchesResolvedSystem : Bool
    exactWrongTypeCulpabilityRequired : Bool
    explicitLiabilityDecisionRequired : Bool
    candidateViolationMayAdmitLiability : Bool
    noViolationMayAdmitLiability : Bool
    admittedViolationAutomaticallyCreatesLiability : Bool
    liabilityAutomaticallySelectsRemedy : Bool

canonicalLiabilityPrerequisiteMeetBoundary : LiabilityPrerequisiteMeetBoundary
canonicalLiabilityPrerequisiteMeetBoundary =
  liability-prerequisite-meet-boundary
    true true true true true true true true true false false false false
