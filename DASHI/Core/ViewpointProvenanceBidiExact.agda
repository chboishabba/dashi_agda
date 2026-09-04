module DASHI.Core.ViewpointProvenanceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- VIEWPOINT / DISCLOSURE-POSITION BIDI CORE
--
-- Purpose: test whether a roster is enriched for a distinctive viewpoint
-- without inferring beliefs from technical work.  A viewpoint assignment must
-- carry provenance strong enough for the claimed subject.
------------------------------------------------------------------------

data ViewpointAxis : Set where
  uapDisclosureSupport
  suppressedOrExoticPropulsionBelief
  transformativeFusionEnergyExpectation
  secrecyOrClassificationCritique
  willingSensitiveTechnicalDisclosure
  hiddenMajorCapabilityBelief
  : ViewpointAxis

data ViewpointProvenance : Set where
  selfStated
  contemporaneousDirectWitness
  contemporaneousDocumentedParticipation
  laterAttribution
  mediaProjection
  : ViewpointProvenance

data ViewpointStatus : Set where
  positive
  negative
  unknown
  contradicted
  : ViewpointStatus

record ViewpointReceipt : Set where
  constructor viewpoint-receipt
  field
    person : String
    axis : ViewpointAxis
    status : ViewpointStatus
    provenance : ViewpointProvenance
    sourceReference : String
    boundedReading : String

open ViewpointReceipt public

------------------------------------------------------------------------
-- BIDI rule: a strong viewpoint claim must compile backward into a receipt
-- whose provenance actually bears on the person's own position.
------------------------------------------------------------------------

record StrongViewpointClaim (receipt : ViewpointReceipt) : Set where
  constructor strong-viewpoint-claim
  field
    isPositive : status receipt ≡ positive
    selfOrDirect :
      (provenance receipt ≡ selfStated) ⊎
      (provenance receipt ≡ contemporaneousDirectWitness)

open StrongViewpointClaim public

record ParticipationWithoutBelief (receipt : ViewpointReceipt) : Set where
  constructor participation-without-belief
  field
    isParticipation : provenance receipt ≡ contemporaneousDocumentedParticipation
    beliefNotPromoted : status receipt ≡ unknown

open ParticipationWithoutBelief public

record ViewpointBoundary : Set where
  constructor viewpoint-boundary
  field
    technicalWorkAutomaticallyCreatesViewpoint : Bool
    technicalWorkAutomaticallyCreatesViewpointIsFalse :
      technicalWorkAutomaticallyCreatesViewpoint ≡ false
    participationAutomaticallyCreatesBelief : Bool
    participationAutomaticallyCreatesBeliefIsFalse :
      participationAutomaticallyCreatesBelief ≡ false
    attributedBeliefEqualsSelfStatedBelief : Bool
    attributedBeliefEqualsSelfStatedBeliefIsFalse :
      attributedBeliefEqualsSelfStatedBelief ≡ false
    posthumousMediaNarrativeCreatesViewpoint : Bool
    posthumousMediaNarrativeCreatesViewpointIsFalse :
      posthumousMediaNarrativeCreatesViewpoint ≡ false

canonicalViewpointBoundary : ViewpointBoundary
canonicalViewpointBoundary = viewpoint-boundary
  false refl
  false refl
  false refl
  false refl
