module DASHI.Biology.AvianMagnetoreceptionRFGoniometerPhasedArrayBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.AvianMagneticFieldPerturbationReceipt as Bio
import DASHI.Biology.MagnetoreceptionSurface as Generic
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as Goniometer
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array
import DASHI.Physics.Foundations.GoniometerPhasedArrayRFSensingCrossPollinationExact as RFBridge
import DASHI.Physics.Foundations.RFSensingThroughWallExact as RFSensing

------------------------------------------------------------------------
-- Apparatus-geometry cross-pollination.
--
-- Goniometers, phased arrays, and RF sensing share useful observation/
-- steering coordinates with magnetic perturbation experiments:
--
--   mechanical angle
--   relative phase
--   relative amplitude
--   electronic steering
--   bounded RF observation.
--
-- This bridge reuses those coordinate owners only.  It does not identify a
-- bird-experiment coil or antenna system with historical RDF hardware, nor
-- infer a receptor mechanism from the apparatus used to perturb the field.
------------------------------------------------------------------------

data ApparatusCoordinateRole : Set where
  mechanicalOrientationRole : ApparatusCoordinateRole
  phaseDifferenceRole : ApparatusCoordinateRole
  amplitudeDifferenceRole : ApparatusCoordinateRole
  electronicSteeringRole : ApparatusCoordinateRole
  boundedRFObservationRole : ApparatusCoordinateRole
  fieldVectorOrientationRole : ApparatusCoordinateRole

data ApparatusToBiologyBoundary : Set where
  noGoniometerHardwareIdentityClaim : ApparatusToBiologyBoundary
  noPhasedArrayHardwareIdentityClaim : ApparatusToBiologyBoundary
  noBearingEqualsFieldVectorClaim : ApparatusToBiologyBoundary
  noSteeringCoordinateEqualsReceptorCoordinateClaim : ApparatusToBiologyBoundary
  noRelativePhaseEqualsRadicalPairPhaseClaim : ApparatusToBiologyBoundary
  noRFObservationEqualsBiologicalStateClaim : ApparatusToBiologyBoundary
  noApparatusChoiceIdentifiesReceptorMechanism : ApparatusToBiologyBoundary

canonicalApparatusRoles : List ApparatusCoordinateRole
canonicalApparatusRoles =
  mechanicalOrientationRole
  ∷ phaseDifferenceRole
  ∷ amplitudeDifferenceRole
  ∷ electronicSteeringRole
  ∷ boundedRFObservationRole
  ∷ fieldVectorOrientationRole
  ∷ []

canonicalApparatusBiologyBoundaries : List ApparatusToBiologyBoundary
canonicalApparatusBiologyBoundaries =
  noGoniometerHardwareIdentityClaim
  ∷ noPhasedArrayHardwareIdentityClaim
  ∷ noBearingEqualsFieldVectorClaim
  ∷ noSteeringCoordinateEqualsReceptorCoordinateClaim
  ∷ noRelativePhaseEqualsRadicalPairPhaseClaim
  ∷ noRFObservationEqualsBiologicalStateClaim
  ∷ noApparatusChoiceIdentifiesReceptorMechanism
  ∷ []

record AvianMagnetoreceptionRFGoniometerPhasedArrayBridge : Set where
  field
    perturbationReceipt :
      Bio.AvianMagneticFieldPerturbationReceipt
        Generic.canonicalMechanismNeutralMagnetoreceptionSurface

    goniometerFirewall :
      Goniometer.GoniometerRoleFirewall

    goniometerFirewallIsCanonical :
      goniometerFirewall ≡ Goniometer.canonicalGoniometerRoleFirewall

    phasedArrayFirewall :
      Array.SteeringDFFirewall

    phasedArrayFirewallIsCanonical :
      phasedArrayFirewall ≡ Array.canonicalSteeringDFFirewall

    crossDomainFirewall :
      RFBridge.CrossDomainAuthorityFirewall

    crossDomainFirewallIsCanonical :
      crossDomainFirewall ≡ RFBridge.canonicalCrossDomainAuthorityFirewall

    rfSensingBoundary :
      RFSensing.RFSensingBoundary

    rfSensingBoundaryIsCanonical :
      rfSensingBoundary ≡ RFSensing.canonicalRFSensingBoundary

    roles :
      List ApparatusCoordinateRole

    rolesAreCanonical :
      roles ≡ canonicalApparatusRoles

    boundaries :
      List ApparatusToBiologyBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalApparatusBiologyBoundaries

    sharedAngleRole :
      Bool

    sharedAngleRoleIsTrue :
      sharedAngleRole ≡ true

    sharedPhaseCoordinate :
      Bool

    sharedPhaseCoordinateIsTrue :
      sharedPhaseCoordinate ≡ true

    apparatusIdentifiesBiologicalMechanism :
      Bool

    apparatusIdentifiesBiologicalMechanismIsFalse :
      apparatusIdentifiesBiologicalMechanism ≡ false

    exactFieldAtReceptorRecovered :
      Bool

    exactFieldAtReceptorRecoveredIsFalse :
      exactFieldAtReceptorRecovered ≡ false

    bridgeReading :
      String

open AvianMagnetoreceptionRFGoniometerPhasedArrayBridge public

canonicalAvianMagnetoreceptionRFGoniometerPhasedArrayBridge :
  AvianMagnetoreceptionRFGoniometerPhasedArrayBridge
canonicalAvianMagnetoreceptionRFGoniometerPhasedArrayBridge =
  record
    { perturbationReceipt =
        Bio.canonicalMechanismNeutralPerturbationReceipt
    ; goniometerFirewall =
        Goniometer.canonicalGoniometerRoleFirewall
    ; goniometerFirewallIsCanonical = refl
    ; phasedArrayFirewall =
        Array.canonicalSteeringDFFirewall
    ; phasedArrayFirewallIsCanonical = refl
    ; crossDomainFirewall =
        RFBridge.canonicalCrossDomainAuthorityFirewall
    ; crossDomainFirewallIsCanonical = refl
    ; rfSensingBoundary =
        RFSensing.canonicalRFSensingBoundary
    ; rfSensingBoundaryIsCanonical = refl
    ; roles = canonicalApparatusRoles
    ; rolesAreCanonical = refl
    ; boundaries = canonicalApparatusBiologyBoundaries
    ; boundariesAreCanonical = refl
    ; sharedAngleRole = true
    ; sharedAngleRoleIsTrue = refl
    ; sharedPhaseCoordinate = true
    ; sharedPhaseCoordinateIsTrue = refl
    ; apparatusIdentifiesBiologicalMechanism = false
    ; apparatusIdentifiesBiologicalMechanismIsFalse = refl
    ; exactFieldAtReceptorRecovered = false
    ; exactFieldAtReceptorRecoveredIsFalse = refl
    ; bridgeReading =
        "Goniometer and phased-array angle/phase coordinates constrain apparatus-side field geometry, while exact receptor exposure and biological mechanism identity remain separate receipt obligations."
    }
