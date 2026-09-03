module DASHI.Cognition.PNF.SensibLawAttributionPropositionOccurrenceBidiExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Interop.SensibLawOntologyTopology as Ontology

------------------------------------------------------------------------
-- BIDI CAMPAIGN 1+2: attribution / proposition status / event occurrence.
--
-- The ontology already owns Claim, Perspective and Event.  This owner welds
-- those exact objects to the orthogonal semantic-status product.  A Claim is
-- therefore interpreted as an assertion ABOUT an event, never as the event or
-- as a truth proof.
------------------------------------------------------------------------

claimProposition : Ontology.Claim → Status.PropositionStatusProduct
claimProposition claim =
  Status.propositionStatusProduct
    (Ontology.StableId.value (Ontology.Claim.claimId claim))
    Status.assertedBySource
    Status.truthUnresolved
    Status.propositionSource
    Status.evidenceNeutral
    Status.sourceEvidence
    Status.modalityKindUnresolved
    Status.modalForceUnresolved
    Status.scopeUnresolved

claimEvent : Ontology.Event → Status.EventStatusProduct
claimEvent event =
  Status.eventStatusProduct
    (Ontology.StableId.value (Ontology.Event.eventId event))
    Status.mentionedEventuality
    Status.eventTime
    Status.scopeUnresolved

record ClaimAttributionOccurrenceWeld
    (claim : Ontology.Claim)
    (perspective : Ontology.Perspective)
    (event : Ontology.Event) : Set where
  constructor claimAttributionOccurrenceWeld
  field
    sameSpeaker :
      Ontology.Claim.assertedBy claim ≡ Ontology.Perspective.speakerId perspective
    sameEvent :
      Ontology.Claim.aboutEvent claim ≡ Ontology.Event.eventId event
    proposition : Status.PropositionStatusProduct
    occurrence : Status.EventStatusProduct
    samePropositionReference :
      Status.propositionReference proposition
      ≡ Ontology.StableId.value (Ontology.Claim.claimId claim)
    sameEventReference :
      Status.eventReference occurrence
      ≡ Ontology.StableId.value (Ontology.Event.eventId event)

open ClaimAttributionOccurrenceWeld public

canonicalClaimAttributionOccurrenceWeld :
  (claim : Ontology.Claim) →
  (perspective : Ontology.Perspective) →
  (event : Ontology.Event) →
  Ontology.Claim.assertedBy claim ≡ Ontology.Perspective.speakerId perspective →
  Ontology.Claim.aboutEvent claim ≡ Ontology.Event.eventId event →
  ClaimAttributionOccurrenceWeld claim perspective event
canonicalClaimAttributionOccurrenceWeld claim perspective event speakerEq eventEq =
  claimAttributionOccurrenceWeld
    speakerEq
    eventEq
    (claimProposition claim)
    (claimEvent event)
    refl
    refl

claimStartsAssertedButTruthUnresolved :
  (claim : Ontology.Claim) →
  Status.propositionStatus (claimProposition claim) ≡ Status.assertedBySource
claimStartsAssertedButTruthUnresolved claim = refl

claimDoesNotStartTruthAdmitted :
  (claim : Ontology.Claim) →
  Status.truthStatus (claimProposition claim) ≡ Status.truthUnresolved
claimDoesNotStartTruthAdmitted claim = refl

claimEventStartsMentionedNotAdmitted :
  (event : Ontology.Event) →
  Status.occurrence (claimEvent event) ≡ Status.mentionedEventuality
claimEventStartsMentionedNotAdmitted event = refl

------------------------------------------------------------------------
-- Hard non-collapse laws.
------------------------------------------------------------------------

data ClaimAssertionIsTruthProof : Set where
data ClaimAboutEventIsOccurrenceProof : Set where
data SpeakerIdentityIsPropositionTruth : Set where

claimAssertionDoesNotProveTruth : ClaimAssertionIsTruthProof → ⊥
claimAssertionDoesNotProveTruth ()

claimReferenceDoesNotProveOccurrence : ClaimAboutEventIsOccurrenceProof → ⊥
claimReferenceDoesNotProveOccurrence ()

speakerIdentityDoesNotProveTruth : SpeakerIdentityIsPropositionTruth → ⊥
speakerIdentityDoesNotProveTruth ()
