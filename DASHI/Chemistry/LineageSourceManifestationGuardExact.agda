module DASHI.Chemistry.LineageSourceManifestationGuardExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Chemistry.LineageCalibrationAttributionEnvelopeExact as Attribution

------------------------------------------------------------------------
-- SAME-OBJECT / LOCATOR GUARD
--
-- A source identity or nearby citation does not pay a coordinate unless the
-- manifestation, locator and role match the exact consumer claim.
------------------------------------------------------------------------

data ManifestationStatus : Set where
  sameObjectManifestationVerified : ManifestationStatus
  sameArticleLocatorUnresolved : ManifestationStatus
  sourceIdentityOnly : ManifestationStatus
  crossSourceAnalogyOnly : ManifestationStatus
  manifestationMismatch : ManifestationStatus

data LocatorStatus : Set where
  exactLocatorVerified : LocatorStatus
  sectionLevelLocator : LocatorStatus
  articleLevelOnly : LocatorStatus
  locatorUnresolved : LocatorStatus

data CoordinateRole : Set where
  reactionIdentityRole : CoordinateRole
  atomMappingRole : CoordinateRole
  electronTransferRole : CoordinateRole
  geometryRole : CoordinateRole
  kineticsRole : CoordinateRole
  fluxRole : CoordinateRole
  biologicalOutcomeRole : CoordinateRole
  prebioticContextRole : CoordinateRole

record SourceCoordinateGuard : Set₁ where
  constructor sourceCoordinateGuard
  field
    envelope : Attribution.ReplayAttributionEnvelope
    manifestationStatus : ManifestationStatus
    locatorStatus : LocatorStatus
    coordinateRole : CoordinateRole
    exactClaimReference : String
    exactSourceLocatorReference : String
    methodMatchReference : String
    contextMatchReference : String
    paid : Bool
    nearbyCitationOnly : Bool
    nearbyCitationOnlyIsFalseWhenPaid : paid ≡ true → nearbyCitationOnly ≡ false

open SourceCoordinateGuard public

chlorReactionIdentityGuard : SourceCoordinateGuard
chlorReactionIdentityGuard =
  sourceCoordinateGuard
    Attribution.chlorEnvelope
    sameObjectManifestationVerified
    sectionLevelLocator
    reactionIdentityRole
    "standard chlor-alkali electrolysis reaction context"
    "Euro Chlor process/electrode-reaction description"
    "industrial process description matches qualitative reaction identity only"
    "membrane/diaphragm cell context; plant-specific kinetics excluded"
    true
    false
    (λ _ → refl)

pahMechanismGuard : SourceCoordinateGuard
pahMechanismGuard =
  sourceCoordinateGuard
    Attribution.pahEnvelope
    sameObjectManifestationVerified
    articleLevelOnly
    reactionIdentityRole
    "BH4/O2/non-heme-iron aromatic hydroxylase mechanism family"
    "Roberts/Fitzpatrick 2013 article"
    "mechanism-family support; replay-specific isotope mapping not located"
    "enzyme-class context only"
    true
    false
    (λ _ → refl)

pbCaGeometryGuard : SourceCoordinateGuard
pbCaGeometryGuard =
  sourceCoordinateGuard
    Attribution.pbCaEnvelope
    sameObjectManifestationVerified
    articleLevelOnly
    geometryRole
    "Pb2+ and Ca2+ protein coordination geometries differ in source structural survey"
    "Kirberger/Yang 2008 article"
    "structural survey matches coordination-geometry claim"
    "protein-site-conditioned evidence; no universal affinity rule"
    true
    false
    (λ _ → refl)

carbonSpecificReactionGuard : SourceCoordinateGuard
carbonSpecificReactionGuard =
  sourceCoordinateGuard
    Attribution.carbonEnvelope
    sourceIdentityOnly
    articleLevelOnly
    reactionIdentityRole
    "specific carbon-bond reaction replay"
    "Astrobiology Primer v2.0"
    "overview supports context, not a specific reaction identity"
    "prebiotic overview only"
    false
    false
    (λ ())

record LineageManifestationBoundary : Set where
  constructor lineageManifestationBoundary
  field
    nearbyCitationPaysCoordinate : Bool
    nearbyCitationPaysCoordinateIsFalse : nearbyCitationPaysCoordinate ≡ false
    sameObjectAndLocatorRequiredForNumericPayment : Bool
    sameObjectAndLocatorRequiredForNumericPaymentIsTrue :
      sameObjectAndLocatorRequiredForNumericPayment ≡ true
    sourceIdentityAlonePaysMethodRole : Bool
    sourceIdentityAlonePaysMethodRoleIsFalse : sourceIdentityAlonePaysMethodRole ≡ false
    sectionLocatorAutomaticallyPaysExactValue : Bool
    sectionLocatorAutomaticallyPaysExactValueIsFalse :
      sectionLocatorAutomaticallyPaysExactValue ≡ false
    crossSourceAnalogyPaysSameObjectClaim : Bool
    crossSourceAnalogyPaysSameObjectClaimIsFalse :
      crossSourceAnalogyPaysSameObjectClaim ≡ false
    unpaidCoordinatesRemainTyped : Bool
    unpaidCoordinatesRemainTypedIsTrue : unpaidCoordinatesRemainTyped ≡ true

open LineageManifestationBoundary public

canonicalLineageManifestationBoundary : LineageManifestationBoundary
canonicalLineageManifestationBoundary =
  lineageManifestationBoundary false refl true refl false refl false refl false refl true refl
