module DASHI.Cognition.PNF.SensibLawNarrativeToLegalGateLiveBidiExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.NarrativeClaimProvenanceExact as ClaimNarrative
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawClaimLatticeNarrativeStatusLiveBidiExact as Narrative
import DASHI.Cognition.PNF.SensibLawClaimAtomOntologyVerticalSliceExact as Vertical
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Legal

------------------------------------------------------------------------
-- LIVE NARRATIVE STATUS -> LEGAL INPUT GATE
--
-- Same event carrier, different discourse/occurrence status.  Candidate legal
-- analysis is allowed for allegations/assertions/denials, but admitted
-- applicability is constructible here only on an established-occurrence route.
------------------------------------------------------------------------

assertedEventStatus : Status.EventStatusProduct
assertedEventStatus = Narrative.eventStatus Narrative.canonicalDogWalkedOccurrence

assertedPropositionStatus : Status.PropositionStatusProduct
assertedPropositionStatus =
  Vertical.CrossCarrierPropositionReceipt.refined Vertical.dogWalkedPropositionLive

assertedCandidateGate : Legal.SemanticLegalInputGate Vertical.dogEvent
assertedCandidateGate =
  Legal.semanticLegalInputGate
    assertedEventStatus
    assertedPropositionStatus
    refl
    Status.applicabilityCandidate
    Legal.assertionCandidateUse

assertedRouteStaysCandidate :
  Legal.SemanticLegalInputGate.resultingApplicability assertedCandidateGate
  ≡ Status.applicabilityCandidate
assertedRouteStaysCandidate = refl

deniedEventStatus : Status.EventStatusProduct
deniedEventStatus = Narrative.eventStatus Narrative.canonicalDogDeniedOccurrence

deniedPropositionStatus : Status.PropositionStatusProduct
deniedPropositionStatus =
  Vertical.CrossCarrierPropositionReceipt.refined Vertical.dogDeniedPropositionLive

deniedCandidateGate : Legal.SemanticLegalInputGate Vertical.dogEvent
deniedCandidateGate =
  Legal.semanticLegalInputGate
    deniedEventStatus
    deniedPropositionStatus
    refl
    Status.applicabilityCandidate
    Legal.denialCandidateUse

deniedRouteStaysCandidate :
  Legal.SemanticLegalInputGate.resultingApplicability deniedCandidateGate
  ≡ Status.applicabilityCandidate
deniedRouteStaysCandidate = refl

allegedNarrative : Narrative.NarrativeModalityStatusReceipt
allegedNarrative =
  Narrative.compileNarrativeModality
    "proposition:dog-walk-alleged"
    "event:dog-walk"
    ClaimNarrative.alleged

allegedCandidateGate : Legal.SemanticLegalInputGate Vertical.dogEvent
allegedCandidateGate =
  Legal.semanticLegalInputGate
    (Narrative.NarrativeModalityStatusReceipt.event allegedNarrative)
    (Narrative.NarrativeModalityStatusReceipt.proposition allegedNarrative)
    refl
    Status.applicabilityCandidate
    Legal.allegationCandidateUse

allegedRouteStaysCandidate :
  Legal.SemanticLegalInputGate.resultingApplicability allegedCandidateGate
  ≡ Status.applicabilityCandidate
allegedRouteStaysCandidate = refl

------------------------------------------------------------------------
-- A finding can support legal establishment while universal truth remains
-- unresolved.  This is intentionally different from truthAdmitted.
------------------------------------------------------------------------

foundEventStatus : Status.EventStatusProduct
foundEventStatus =
  Status.eventStatusProduct
    "event:dog-walk"
    Status.occurrenceAdmitted
    Status.eventTime
    Status.scopeResolved

foundPropositionStatus : Status.PropositionStatusProduct
foundPropositionStatus =
  Status.propositionStatusProduct
    "proposition:dog-walk-finding"
    Status.foundAsFact
    Status.truthUnresolved
    Status.propositionSource
    Status.evidenceFor
    Status.documentaryEvidence
    Status.modalityKindUnresolved
    Status.modalForceUnresolved
    Status.scopeResolved

findingEstablishedGate : Legal.SemanticLegalInputGate Vertical.dogEvent
findingEstablishedGate =
  Legal.semanticLegalInputGate
    foundEventStatus
    foundPropositionStatus
    refl
    Status.applicabilityAdmitted
    Legal.establishedFindingUse

findingMayEnterAdmittedApplicability :
  Legal.SemanticLegalInputGate.resultingApplicability findingEstablishedGate
  ≡ Status.applicabilityAdmitted
findingMayEnterAdmittedApplicability = refl

findingStillNotUniversalTruth :
  Status.truthStatus foundPropositionStatus ≡ Status.truthUnresolved
findingStillNotUniversalTruth = refl

------------------------------------------------------------------------
-- No candidate discourse route can be silently re-described as established.
------------------------------------------------------------------------

data AllegationGateEqualsEstablishedGate : Set where
data AssertionGateEqualsEstablishedGate : Set where
data DenialGateEqualsEstablishedGate : Set where

allegationGateDoesNotBecomeEstablished : AllegationGateEqualsEstablishedGate → ⊥
allegationGateDoesNotBecomeEstablished ()

assertionGateDoesNotBecomeEstablished : AssertionGateEqualsEstablishedGate → ⊥
assertionGateDoesNotBecomeEstablished ()

denialGateDoesNotBecomeEstablished : DenialGateEqualsEstablishedGate → ⊥
denialGateDoesNotBecomeEstablished ()
