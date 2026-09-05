module DASHI.Core.OpenScienceKnowledgeReleaseBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ViewpointProvenanceBidiExact as V

------------------------------------------------------------------------
-- OPEN-SCIENCE / KNOWLEDGE-RELEASE BIDI CORE
--
-- Parent hypothesis for publication, open technical artefacts, public teaching,
-- disclosure advocacy and anti-suppression positions.  The crucial distinction
-- is between ordinary public dissemination and an evidenced crossing from a
-- genuinely restricted/private state into public circulation.
------------------------------------------------------------------------

data OpenScienceAxis : Set where
  publicTechnicalPublication
  openCodeDataOrMethods
  publicTechnicalEducation
  disclosureOrTransparencyAdvocacy
  suppressionOrSecrecyCritique
  restrictedToPublicBoundaryCrossing
  : OpenScienceAxis

data OpenScienceMode : Set where
  behaviour
  explicitBelief
  institutionalParticipation
  : OpenScienceMode

data OpenScienceProvenance : Set where
  selfStatement
  publicArtifact
  institutionalRelease
  contemporaneousDirectWitness
  documentedParticipation
  laterAttribution
  mediaProjection
  : OpenScienceProvenance

data OpenScienceStatus : Set where
  positive
  negative
  unknown
  contradicted
  : OpenScienceStatus

record OpenScienceReceipt : Set where
  constructor open-science-receipt
  field
    person : String
    axis : OpenScienceAxis
    mode : OpenScienceMode
    status : OpenScienceStatus
    provenance : OpenScienceProvenance
    sourceReference : String
    boundedReading : String

open OpenScienceReceipt public

------------------------------------------------------------------------
-- Strong ordinary-open-science claim: evidence of an actual public behaviour
-- or the person's own explicit openness/disclosure position.
------------------------------------------------------------------------

record StrongOpenScienceClaim (receipt : OpenScienceReceipt) : Set where
  constructor strong-open-science-claim
  field
    isPositive : status receipt ≡ positive
    directCarrier :
      (provenance receipt ≡ selfStatement) ⊎
      (provenance receipt ≡ publicArtifact) ⊎
      (provenance receipt ≡ institutionalRelease) ⊎
      (provenance receipt ≡ contemporaneousDirectWitness)

open StrongOpenScienceClaim public

------------------------------------------------------------------------
-- O6 is intentionally stricter.  A public paper/patent/talk does not establish
-- that material had previously been restricted.  The reverse direction must
-- acquire both sides of the boundary.
------------------------------------------------------------------------

record RestrictedToPublicTransfer (receipt : OpenScienceReceipt) : Set where
  constructor restricted-to-public-transfer
  field
    correctAxis : axis receipt ≡ restrictedToPublicBoundaryCrossing
    isPositive : status receipt ≡ positive
    priorRestrictionReference : String
    releaseReference : String
    sameKnowledgeObjectReference : String

open RestrictedToPublicTransfer public

------------------------------------------------------------------------
-- Viewpoint x-pollination is PARTIAL, not total.
--
-- Only viewpoint coordinates whose semantics directly concern disclosure or
-- secrecy can bridge into the open-science parent without a second independent
-- receipt.  Fusion optimism, hidden-capability belief and exotic-propulsion
-- belief do not by themselves establish openness.
------------------------------------------------------------------------

data ViewpointSupportsOpenAxis : V.ViewpointAxis → OpenScienceAxis → Set where
  uapDisclosureSupportsTransparency :
    ViewpointSupportsOpenAxis
      V.uapDisclosureSupport
      disclosureOrTransparencyAdvocacy
  secrecyCritiqueSupportsOpenCritique :
    ViewpointSupportsOpenAxis
      V.secrecyOrClassificationCritique
      suppressionOrSecrecyCritique
  willingDisclosureSupportsTransparency :
    ViewpointSupportsOpenAxis
      V.willingSensitiveTechnicalDisclosure
      disclosureOrTransparencyAdvocacy

record ViewpointToOpenScienceBridge (v : V.ViewpointReceipt) (o : OpenScienceReceipt) : Set where
  constructor viewpoint-to-open-science-bridge
  field
    samePerson : V.person v ≡ person o
    semanticBridge : ViewpointSupportsOpenAxis (V.axis v) (axis o)
    viewpointStrong : V.StrongViewpointClaim v
    bridgeReference : String

open ViewpointToOpenScienceBridge public

------------------------------------------------------------------------
-- BIDI acquisition: a proposed open-science selection feature must reverse to
-- an exact missing receipt, rather than infer openness from prestige or field.
------------------------------------------------------------------------

data OpenScienceAcquisitionTarget : Set where
  publicationReceipt
  openArtifactReceipt
  publicTeachingReceipt
  disclosureAdvocacyReceipt
  antiSuppressionReceipt
  priorRestrictionReceipt
  publicReleaseReceipt
  sameKnowledgeObjectWeld
  matchedOpenScienceControls
  : OpenScienceAcquisitionTarget

record OpenScienceReverseObligation : Set where
  constructor open-science-reverse-obligation
  field
    personOrRole : String
    target : OpenScienceAcquisitionTarget
    preferredEvidence : String
    whatItCanPromote : String
    whatItCannotPromote : String

open OpenScienceReverseObligation public

record OpenScienceBoundary : Set where
  constructor open-science-boundary
  field
    publicationAutomaticallyMeansAntiSecrecyBelief : Bool
    publicationAutomaticallyMeansAntiSecrecyBeliefIsFalse :
      publicationAutomaticallyMeansAntiSecrecyBelief ≡ false
    publicArtifactAutomaticallyMeansRestrictedBoundaryCrossed : Bool
    publicArtifactAutomaticallyMeansRestrictedBoundaryCrossedIsFalse :
      publicArtifactAutomaticallyMeansRestrictedBoundaryCrossed ≡ false
    disclosureAdvocacyProvesPriorPossessionOfRestrictedMaterial : Bool
    disclosureAdvocacyProvesPriorPossessionOfRestrictedMaterialIsFalse :
      disclosureAdvocacyProvesPriorPossessionOfRestrictedMaterial ≡ false
    institutionalPublicationProvesPersonalOpenScienceIdeology : Bool
    institutionalPublicationProvesPersonalOpenScienceIdeologyIsFalse :
      institutionalPublicationProvesPersonalOpenScienceIdeology ≡ false
    fusionOptimismAutomaticallyMeansOpenScience : Bool
    fusionOptimismAutomaticallyMeansOpenScienceIsFalse :
      fusionOptimismAutomaticallyMeansOpenScience ≡ false
    hiddenCapabilityBeliefAutomaticallyMeansOpenScience : Bool
    hiddenCapabilityBeliefAutomaticallyMeansOpenScienceIsFalse :
      hiddenCapabilityBeliefAutomaticallyMeansOpenScience ≡ false
    matchedControlsRequiredForOpenScienceEnrichment : Bool
    matchedControlsRequiredForOpenScienceEnrichmentIsTrue :
      matchedControlsRequiredForOpenScienceEnrichment ≡ true

canonicalOpenScienceBoundary : OpenScienceBoundary
canonicalOpenScienceBoundary = open-science-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl
