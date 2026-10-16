{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravitySICalibrationDonorMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.EinsteinPhysicalCouplingCalibrationExact as Einstein
import DASHI.Physics.ExoticGravity.AntigravityCODATA2022GAuthorityAdmissionExact as GAuthority
import DASHI.Physics.ExoticGravity.AntigravityStressLengthSquaredTargetIntervalExact as ScaleTarget

------------------------------------------------------------------------
-- SI / PHYSICAL CALIBRATION DONOR MAX-CUT
--
-- Current master already owns a deterministic replay candidate for
--
--   kappa = 8*pi*G/c^4
--
-- in the energy-density convention, backed by a vendored CODATA-2022/NIST
-- artifact and checksum.  This branch additionally carries a separately
-- attributed NIST/CODATA source admission for the same G value/uncertainty and
-- instantiates the existing AcceptedPhysicalEinsteinCoupling ABI with concrete
-- provenance objects.
--
-- Attribution boundary:
--   * the NIST/CODATA citation does not create authority by itself;
--   * AntigravityCODATA2022GAuthorityAdmissionExact is the explicit repository
--     consumer-admission step;
--   * G remains measured with retained uncertainty, never exact by fiat.
--
-- The reciprocal/order algebra for the remaining source/device scale is also
-- compiler-owned now.  For any rational diagnostic kappa point inside the
-- accepted enclosure and positive source magnitude C, the required
-- stress*length^2 product to hit target Lambda lies in
--
--   [ Lambda / (kappa_upper*C), Lambda / (kappa_lower*C) ].
--
-- This diagnostic theorem does NOT promote the measured physical kappa to an
-- exact rational point.  It only removes residual interval arithmetic from P2.
-- The one remaining physical SI package is therefore same-apparatus
-- identification/measurement of the source-native stress*length^2 product.
------------------------------------------------------------------------

vendoredCODATAEinsteinCouplingCandidateAvailable : Bool
vendoredCODATAEinsteinCouplingCandidateAvailable =
  Einstein.gAuthorityMetadataPresent
    Einstein.canonicalEinsteinPhysicalCouplingCandidate

exactSpeedOfLightIsNotCalibrationBlocker : Bool
exactSpeedOfLightIsNotCalibrationBlocker = true

newEinsteinCouplingConventionRequired : Bool
newEinsteinCouplingConventionRequired = false

acceptedMeasuredGAuthorityPaid : Bool
acceptedMeasuredGAuthorityPaid = GAuthority.acceptedMeasuredGAuthorityPaid

acceptedMeasuredGAuthorityStillRequired : Bool
acceptedMeasuredGAuthorityStillRequired =
  GAuthority.acceptedMeasuredGAuthorityStillRequired

acceptedPhysicalEinsteinCouplingAvailable : Bool
acceptedPhysicalEinsteinCouplingAvailable =
  GAuthority.acceptedPhysicalEinsteinCouplingAvailable

requiredStressLengthSquaredIntervalAlgebraOwned : Bool
requiredStressLengthSquaredIntervalAlgebraOwned = true

rationalPointDiagnosticPromotesMeasuredKappaToExact : Bool
rationalPointDiagnosticPromotesMeasuredKappaToExact =
  ScaleTarget.rationalPointDiagnosticPromotesMeasuredKappaToExact

sourceStressLengthSquaredScaleStillRequired : Bool
sourceStressLengthSquaredScaleStillRequired =
  ScaleTarget.remainingP2DatumIsSameApparatusStressLengthSquaredProduct

separateStressAndLengthIdentificationRequired : Bool
separateStressAndLengthIdentificationRequired = false

physicalEinsteinCouplingAlreadyPromoted : Bool
physicalEinsteinCouplingAlreadyPromoted =
  acceptedPhysicalEinsteinCouplingAvailable

globalCandidatePromotionFlagStillFalse : Bool
globalCandidatePromotionFlagStillFalse =
  Einstein.physicalEinsteinCouplingPromoted
    Einstein.canonicalEinsteinPhysicalCouplingCandidate

exactNewtonianGClaimed : Bool
exactNewtonianGClaimed = GAuthority.exactNewtonianGClaimed

remainingSICalibrationPhysicalPackageCount : Nat
remainingSICalibrationPhysicalPackageCount = 1

record AntigravitySICalibrationFrontier : Set where
  constructor antigravity-si-calibration-frontier
  field
    vendoredCandidatePresent : Bool
    exactCOpen : Bool
    newConventionOpen : Bool
    acceptedMeasuredGOpen : Bool
    requiredScaleIntervalAlgebraOpen : Bool
    stressLengthSquaredProductOpen : Bool
    separateStressScaleOpen : Bool
    separateLengthScaleOpen : Bool
    physicalKappaAlreadyPromoted : Bool
    globalCandidateFlagMutated : Bool
    exactGClaimed : Bool
    remainingPhysicalPackageCount : Nat

canonicalAntigravitySICalibrationFrontier : AntigravitySICalibrationFrontier
canonicalAntigravitySICalibrationFrontier =
  antigravity-si-calibration-frontier
    true false false false false true false false true false false 1

acceptedMeasuredGAuthorityStillRequiredIsFalse :
  acceptedMeasuredGAuthorityStillRequired ≡ false
acceptedMeasuredGAuthorityStillRequiredIsFalse =
  GAuthority.acceptedMeasuredGAuthorityStillRequiredIsFalse

newEinsteinCouplingConventionRequiredIsFalse :
  newEinsteinCouplingConventionRequired ≡ false
newEinsteinCouplingConventionRequiredIsFalse = refl

requiredStressLengthSquaredIntervalAlgebraOwnedIsTrue :
  requiredStressLengthSquaredIntervalAlgebraOwned ≡ true
requiredStressLengthSquaredIntervalAlgebraOwnedIsTrue = refl

rationalPointDiagnosticPromotesMeasuredKappaToExactIsFalse :
  rationalPointDiagnosticPromotesMeasuredKappaToExact ≡ false
rationalPointDiagnosticPromotesMeasuredKappaToExactIsFalse = refl

separateStressAndLengthIdentificationRequiredIsFalse :
  separateStressAndLengthIdentificationRequired ≡ false
separateStressAndLengthIdentificationRequiredIsFalse = refl

exactNewtonianGClaimedIsFalse : exactNewtonianGClaimed ≡ false
exactNewtonianGClaimedIsFalse = GAuthority.exactNewtonianGClaimedIsFalse
