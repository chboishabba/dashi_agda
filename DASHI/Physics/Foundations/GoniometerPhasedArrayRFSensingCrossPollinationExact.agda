module DASHI.Physics.Foundations.GoniometerPhasedArrayRFSensingCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as G
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as A
import DASHI.Physics.Foundations.RFSensingThroughWallExact as RF

------------------------------------------------------------------------
-- The observed instrument is retained as a contextual provenance hypothesis,
-- not promoted to an exact hardware, unit, system, or mission identification.
------------------------------------------------------------------------

record GoniometerProvenanceStatus : Set where
  constructor goniometer-provenance-status
  field
    contextSupportsRDFOrigin : Bool
    contextSupportsRDFOriginIsTrue : contextSupportsRDFOrigin ≡ true
    exactHardwareIdentified : Bool
    exactHardwareIdentifiedIsFalse : exactHardwareIdentified ≡ false
    exactOperationalUseIdentified : Bool
    exactOperationalUseIdentifiedIsFalse : exactOperationalUseIdentified ≡ false

open GoniometerProvenanceStatus public

canonicalObservedGoniometerProvenance : GoniometerProvenanceStatus
canonicalObservedGoniometerProvenance =
  goniometer-provenance-status true refl false refl false refl

------------------------------------------------------------------------
-- Cross-pollination: historical/mechanical and modern electronic paths may
-- share an angle-observation role without sharing hardware identity.
------------------------------------------------------------------------

mechanicalGoniometerRole :
  G.implementationRole G.mechanicalAngleReadout ≡ G.angleEstimationRole
mechanicalGoniometerRole = refl

digitalBeamformingRole :
  G.implementationRole G.digitalBeamforming ≡ G.angleEstimationRole
digitalBeamformingRole = refl

arrayPhysicalAndElectronicCoordinatesRemainDistinct :
  A.arrayFaceOrientation ≡ A.electronicSteeringCoordinate → ⊥
arrayPhysicalAndElectronicCoordinatesRemainDistinct =
  A.physicalOrientationIsNotElectronicSteering

arrayBearingStillDoesNotRecoverExactWorld :
  ¬ A.ArrayBearingDeterminesExactEmitterWorld
arrayBearingStillDoesNotRecoverExactWorld =
  A.arrayBearingDoesNotDetermineExactEmitterWorld

rfObservationStillDoesNotRecoverExactHumanWorld :
  ¬ RF.RFObservationDeterminesExactHumanWorld
rfObservationStillDoesNotRecoverExactHumanWorld =
  RF.rfObservationDoesNotDetermineExactHumanWorld

record CrossDomainAuthorityFirewall : Set where
  constructor cross-domain-authority-firewall
  field
    goniometerContextProvesExactSystem : Bool
    goniometerContextProvesExactSystemIsFalse :
      goniometerContextProvesExactSystem ≡ false
    phasedArrayBearingProvesExactEmitterIdentity : Bool
    phasedArrayBearingProvesExactEmitterIdentityIsFalse :
      phasedArrayBearingProvesExactEmitterIdentity ≡ false
    throughWallRFObservationProvesExactIdentity : Bool
    throughWallRFObservationProvesExactIdentityIsFalse :
      throughWallRFObservationProvesExactIdentity ≡ false
    sensingCapabilityCreatesOperationalAuthority : Bool
    sensingCapabilityCreatesOperationalAuthorityIsFalse :
      sensingCapabilityCreatesOperationalAuthority ≡ false

open CrossDomainAuthorityFirewall public

canonicalCrossDomainAuthorityFirewall : CrossDomainAuthorityFirewall
canonicalCrossDomainAuthorityFirewall =
  cross-domain-authority-firewall false refl false refl false refl false refl
