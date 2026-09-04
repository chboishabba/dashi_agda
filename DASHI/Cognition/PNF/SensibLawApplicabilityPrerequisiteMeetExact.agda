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

------------------------------------------------------------------------
-- APPLICABILITY PREREQUISITE MEET
--
-- The legacy WrongTypeApplicabilityReceipt retains string references for
-- temporal/jurisdiction/authority/etc.  This owner strengthens construction:
-- those references are downstream metadata only.  A legal applicability meet
-- may run here only after exact same-state prerequisite receipts exist.
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
    sameEvent :
      Ontology.WrongTypeInterpretation.interpretedEvent interpretation
      ≡ Ontology.Event.eventId event
    sameWrongType :
      Ontology.WrongTypeInterpretation.interpretedAs interpretation
      ≡ Ontology.WrongType.wrongTypeId wrongType
    sameSystem :
      Ontology.WrongTypeInterpretation.underSystem interpretation
      ≡ Ontology.WrongType.definingSystem wrongType
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

------------------------------------------------------------------------
-- The meet preserves the semantic input gate; prerequisite closure does not
-- upgrade an assertion/allegation candidate into admitted occurrence/truth.
------------------------------------------------------------------------

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
    stringReferencesAloneSuffice : Bool
    prerequisiteClosureAdmitsTruth : Bool

canonicalApplicabilityPrerequisiteMeetBoundary : ApplicabilityPrerequisiteMeetBoundary
canonicalApplicabilityPrerequisiteMeetBoundary =
  applicability-prerequisite-meet-boundary
    true true true true true true true false false
