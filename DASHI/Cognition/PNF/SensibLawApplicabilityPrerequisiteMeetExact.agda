module DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact where

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
import DASHI.Cognition.PNF.SensibLawScopeCompositionBidiExact as Scope

------------------------------------------------------------------------
-- APPLICABILITY PREREQUISITE MEET
--
-- All prerequisite receipts must not merely inhabit the same state: they must
-- be welded to the same proposition/event/legal-system objects.  This blocks a
-- mixed bundle assembled from individually valid receipts about unrelated
-- objects.
------------------------------------------------------------------------

record ApplicabilityPrerequisiteBundle
    (state : Status.SemanticCommitmentState) : Set where
  constructor applicabilityPrerequisiteBundle
  field
    proposition : Bridge.PropositionReceiptInState state
    occurrence : Bridge.OccurrenceReceiptInState state
    documentContext : Bridge.DocumentContextReceiptInState state
    resolvedEvidence : Evidence.ResolvedLegalEvidenceReceiptInState state
    legalSourceAuthority : Authority.LegalSourceAuthorityReceiptInState state
    resolvedJurisdiction : Jurisdiction.LegalJurisdictionReceiptInState state
    resolvedScope : Bridge.ResolvedScopeReceiptInState state

    sameEvidenceProposition :
      Evidence.propositionStatus resolvedEvidence
      ≡ Status.proposition (Bridge.receipt proposition)
    sameEvidenceEvent :
      Evidence.eventStatus resolvedEvidence
      ≡ Status.event (Bridge.receipt occurrence)
    sameDocumentProposition :
      Bridge.refinedProposition documentContext
      ≡ Status.proposition (Bridge.receipt proposition)
    sameScopeProposition :
      Scope.proposition (Bridge.receipt resolvedScope)
      ≡ Status.proposition (Bridge.receipt proposition)
    sameScopeEvent :
      Scope.event (Bridge.receipt resolvedScope)
      ≡ Status.event (Bridge.receipt occurrence)
    sameAuthorityJurisdictionLegalStatus :
      Authority.legalStatus legalSourceAuthority
      ≡ Jurisdiction.legalStatus resolvedJurisdiction
    sameAuthorityJurisdictionSystem :
      Authority.system legalSourceAuthority
      ≡ Jurisdiction.system resolvedJurisdiction

    bundleReference : String

open ApplicabilityPrerequisiteBundle public

record ApplicabilityMeetInput
    (state : Status.SemanticCommitmentState) : Set where
  constructor applicabilityMeetInput
  field
    prerequisites : ApplicabilityPrerequisiteBundle state
    event : Ontology.Event
    wrongType : Ontology.WrongType
    interpretation : Ontology.WrongTypeInterpretation
    semanticInput : Legal.SemanticLegalInputGate event
    legalStatus : Status.LegalStatusProduct
    legalStatusMembership : Bridge._∈_ legalStatus (Status.legalStatuses state)
    meetLegalStatusMatchesAuthority :
      legalStatus ≡ Authority.legalStatus (legalSourceAuthority prerequisites)
    meetLegalStatusMatchesJurisdiction :
      legalStatus ≡ Jurisdiction.legalStatus (resolvedJurisdiction prerequisites)
    sameEvent :
      Ontology.WrongTypeInterpretation.interpretedEvent interpretation
      ≡ Ontology.Event.eventId event
    sameWrongType :
      Ontology.WrongTypeInterpretation.interpretedAs interpretation
      ≡ Ontology.WrongType.wrongTypeId wrongType
    sameSystem :
      Ontology.WrongTypeInterpretation.underSystem interpretation
      ≡ Ontology.WrongType.definingSystem wrongType
    meetSystemMatchesResolvedSystem :
      Ontology.WrongType.definingSystem wrongType
      ≡ Ontology.LegalSystem.systemId
          (Authority.system (legalSourceAuthority prerequisites))
    typedMeetReference : String
    temporalReference : String
    exceptionReference : String

open ApplicabilityMeetInput public

compileApplicabilityMeet :
  ∀ {state} →
  ApplicabilityMeetInput state →
  Legal.WrongTypeApplicabilityReceipt
compileApplicabilityMeet input =
  Legal.wrongTypeApplicabilityReceipt
    (event input)
    (wrongType input)
    (interpretation input)
    (semanticInput input)
    (legalStatus input)
    (sameEvent input)
    (sameWrongType input)
    (sameSystem input)
    (Legal.SemanticLegalInputGate.resultingApplicability (semanticInput input))
    refl
    (typedMeetReference input)
    (temporalReference input)
    (Jurisdiction.jurisdictionReference
      (resolvedJurisdiction (prerequisites input)))
    (exceptionReference input)
    (Authority.authorityReference
      (legalSourceAuthority (prerequisites input)))

compiledApplicabilityMatchesSemanticGate :
  ∀ {state} (input : ApplicabilityMeetInput state) →
  Legal.resultingApplicability (compileApplicabilityMeet input)
  ≡ Legal.SemanticLegalInputGate.resultingApplicability (semanticInput input)
compiledApplicabilityMatchesSemanticGate input = refl

data StringsAloneAuthorizeApplicabilityMeet : Set where
data MissingResolvedEvidenceStillAllowsMeet : Set where
data MissingAuthorityStillAllowsMeet : Set where
data MissingResolvedScopeStillAllowsMeet : Set where
data MissingResolvedJurisdictionStillAllowsMeet : Set where
data MixedObjectReceiptsAuthorizeApplicabilityMeet : Set where
data MismatchedLegalStatusAuthorizesApplicabilityMeet : Set where
data MismatchedLegalSystemAuthorizesApplicabilityMeet : Set where
data PrerequisiteClosureAdmitsTruth : Set where

stringsAloneDoNotAuthorizeMeet : StringsAloneAuthorizeApplicabilityMeet → ⊥
stringsAloneDoNotAuthorizeMeet ()
missingResolvedEvidenceBlocksMeet : MissingResolvedEvidenceStillAllowsMeet → ⊥
missingResolvedEvidenceBlocksMeet ()
missingAuthorityBlocksMeet : MissingAuthorityStillAllowsMeet → ⊥
missingAuthorityBlocksMeet ()
missingResolvedScopeBlocksMeet : MissingResolvedScopeStillAllowsMeet → ⊥
missingResolvedScopeBlocksMeet ()
missingResolvedJurisdictionBlocksMeet : MissingResolvedJurisdictionStillAllowsMeet → ⊥
missingResolvedJurisdictionBlocksMeet ()
mixedObjectReceiptsDoNotAuthorizeMeet : MixedObjectReceiptsAuthorizeApplicabilityMeet → ⊥
mixedObjectReceiptsDoNotAuthorizeMeet ()
mismatchedLegalStatusDoesNotAuthorizeMeet : MismatchedLegalStatusAuthorizesApplicabilityMeet → ⊥
mismatchedLegalStatusDoesNotAuthorizeMeet ()
mismatchedLegalSystemDoesNotAuthorizeMeet : MismatchedLegalSystemAuthorizesApplicabilityMeet → ⊥
mismatchedLegalSystemDoesNotAuthorizeMeet ()
prerequisiteClosureDoesNotAdmitTruth : PrerequisiteClosureAdmitsTruth → ⊥
prerequisiteClosureDoesNotAdmitTruth ()

record ApplicabilityPrerequisiteMeetBoundary : Set where
  constructor applicability-prerequisite-meet-boundary
  field
    exactPropositionRequired : Bool
    exactOccurrenceRequired : Bool
    documentContextRequired : Bool
    resolvedEvidenceRequired : Bool
    legalSourceAuthorityRequired : Bool
    resolvedJurisdictionRequired : Bool
    resolvedScopeRequired : Bool
    crossReceiptSameObjectWeldsRequired : Bool
    authorityJurisdictionSameLegalStatusRequired : Bool
    authorityJurisdictionSameLegalSystemRequired : Bool
    meetLegalStatusMustMatchPrerequisites : Bool
    meetWrongTypeSystemMustMatchResolvedSystem : Bool
    stringReferencesAloneSuffice : Bool
    prerequisiteClosureAdmitsTruth : Bool

canonicalApplicabilityPrerequisiteMeetBoundary : ApplicabilityPrerequisiteMeetBoundary
canonicalApplicabilityPrerequisiteMeetBoundary =
  applicability-prerequisite-meet-boundary
    true true true true true true true true true true true true false false
