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
-- Viewpoint x-pollination.  These are parent/child semantic correspondences,
-- not automatic evidence promotion.  A V4/V5 viewpoint receipt still has to
-- satisfy its own provenance requirements before an open-science claim is made.
------------------------------------------------------------------------

viewpointParentAxis : V.ViewpointAxis → OpenScienceAxis
viewpointParentAxis V.uapDisclosureSupport = disclosureOrTransparencyAdvocacy
viewpointParentAxis V.suppressedOrExoticPropulsionBelief = suppressionOrSecrecyCritique
viewpointParentAxis V.transformativeFusionEnergyExpectation = publicTechnicalEducation
viewpointParentAxis V.secrecyOrClassificationCritique = suppressionOrSecrecyCritique
viewpointParentAxis V.willingSensitiveTechnicalDisclosure = disclosureOrTransparencyAdvocacy
viewpointParentAxis V.hiddenMajorCapabilityBelief = suppressionOrSecrecyCritique

record ViewpointToOpenScienceBridge (v : V.ViewpointReceipt) (o : OpenScienceReceipt) : Set where
  constructor viewpoint-to-open-science-bridge
  field
    samePerson : V.person v ≡ person o
    parentAxisAgrees : viewpointParentAxis (V.axis v) ≡ axis o
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
    matchedControlsRequiredForOpenScienceEnrichment : Bool
    matchedControlsRequiredForOpenScienceEnrichmentIsTrue :
      matchedControlsRequiredForOpenScienceEnrichment ≡ true

canonicalOpenScienceBoundary : OpenScienceBoundary
canonicalOpenScienceBoundary = open-science-boundary
  false refl
  false refl
  false refl
  false refl
  true refl
