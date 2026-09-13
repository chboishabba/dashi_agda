module DASHI.Astronomy.LocalGroupFirstLightArtifactObservationExact where

open import DASHI.Core.Prelude
open import DASHI.Astronomy.LocalGroupVirtualObservatoryFirstLightSourceExact
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- What is visibly present in the supplied first-light image artifact.
-- This is an artifact-observation layer, not a scientific validation layer.
------------------------------------------------------------------------

data ArtifactObservationKind : Set where
  visibleTitle : ArtifactObservationKind
  visibleAxis : ArtifactObservationKind
  visibleLegend : ArtifactObservationKind
  visibleAnnotation : ArtifactObservationKind
  visibleRecipeText : ArtifactObservationKind
  visibleCaveat : ArtifactObservationKind

record ArtifactObservation : Set where
  constructor artifactObservation
  field
    kind : ArtifactObservationKind
    transcription : String
    scientificPromotionAllowed : Bool

open ArtifactObservation public

firstLightTitleObservation : ArtifactObservation
firstLightTitleObservation = artifactObservation
  visibleTitle
  "First light: the Local Group census in the model frame (McConnachie 2012 members)"
  false

firstLightXYAxes : ArtifactObservation
firstLightXYAxes = artifactObservation
  visibleAxis
  "x [kpc] versus y [kpc]"
  false

firstLightXZAxes : ArtifactObservation
firstLightXZAxes = artifactObservation
  visibleAxis
  "x [kpc] versus z [kpc]"
  false

firstLightYZAxes : ArtifactObservation
firstLightYZAxes = artifactObservation
  visibleAxis
  "y [kpc] versus z [kpc]"
  false

firstLightNamedMarkers : ArtifactObservation
firstLightNamedMarkers = artifactObservation
  visibleLegend
  "visible legend/annotations distinguish MW, M31, Rest, no published error, Sun, Galactic centre, M31, LG barycentre (model), and LG barycentre Sun-M31 midpoint (McConnachie 2012 Note 10, as measured)"
  false

firstLightFrameText : ArtifactObservation
firstLightFrameText = artifactObservation
  visibleRecipeText
  "frame: Galactocentric (astropy), built from catalog rows (recipe 0001)"
  false

firstLightMemberText : ArtifactObservation
firstLightMemberText = artifactObservation
  visibleRecipeText
  "members: Entity vizier:J/AJ/144/4; positions table1 J2000, distances from (m-M)_0 with published errors"
  false

firstLightColourText : ArtifactObservation
firstLightColourText = artifactObservation
  visibleRecipeText
  "colours: categorical, declared (MW, M31, Rest), opaque 5 Ito"
  false

firstLightAdmissibilityText : ArtifactObservation
firstLightAdmissibilityText = artifactObservation
  visibleCaveat
  "admissibility: members: single institution (NRC Herzberg, McConnachie 2012); not independently confirmed, crosswalk pending (ADR-0001)"
  false

firstLightBarycentreCaveat : ArtifactObservation
firstLightBarycentreCaveat = artifactObservation
  visibleCaveat
  "barycentres: model: Galactic centre-M31 midpoint; McConnachie 2012 Note 10 as measured = Sun-M31 midpoint, separation 4.1385 kpc (R_0?)"
  false

firstLightPublishedModulusErrorCaveat : ArtifactObservation
firstLightPublishedModulusErrorCaveat = artifactObservation
  visibleCaveat
  "no published modulus error: Pisces II, Andromeda XXII"
  false

artifactTextImpliesUnderlyingProducerAcquired : ArtifactObservation → Bool
artifactTextImpliesUnderlyingProducerAcquired _ = false

artifactTextImpliesUnderlyingProducerAcquiredIsFalse :
  (o : ArtifactObservation) →
  artifactTextImpliesUnderlyingProducerAcquired o ≡ false
artifactTextImpliesUnderlyingProducerAcquiredIsFalse o = refl

visibleRecipeTextImpliesRecipeVerified : ArtifactObservation → Bool
visibleRecipeTextImpliesRecipeVerified _ = false

visibleRecipeTextImpliesRecipeVerifiedIsFalse :
  (o : ArtifactObservation) →
  visibleRecipeTextImpliesRecipeVerified o ≡ false
visibleRecipeTextImpliesRecipeVerifiedIsFalse o = refl

privatePostAttributionRemainsControlled : Bool
privatePostAttributionRemainsControlled = true

privatePostAttributionRemainsControlledIsTrue :
  privatePostAttributionRemainsControlled ≡ true
privatePostAttributionRemainsControlledIsTrue = refl

privateServerLocatorMayBePublishedFromArtifact : Bool
privateServerLocatorMayBePublishedFromArtifact = false

privateServerLocatorMayBePublishedFromArtifactIsFalse :
  privateServerLocatorMayBePublishedFromArtifact ≡ false
privateServerLocatorMayBePublishedFromArtifactIsFalse = refl
