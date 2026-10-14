{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravitySICalibrationDonorMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.EinsteinPhysicalCouplingCalibrationExact as Einstein
import DASHI.Physics.ExoticGravity.AntigravityCODATA2022GAuthorityAdmissionExact as GAuthority

------------------------------------------------------------------------
-- SI / PHYSICAL CALIBRATION DONOR MAX-CUT
--
-- Current master already owns a deterministic replay candidate for
--
--   kappa = 8*pi*G/c^4
--
-- in the energy-density convention, backed by a vendored CODATA-2022/NIST
-- artifact and checksum.  This branch now additionally carries a separately
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
-- Consequently accepted measured-G authority is no longer an open leaf for
-- this antigravity consumer.  The remaining physical SI leaf is the
-- source-native stress*length^2 scale seen by the Kottler consumer, plus the
-- same-state source/device identification performed outside this SI owner.
------------------------------------------------------------------------

vendoredCODATAEinsteinCouplingCandidateAvailable : Bool
vendoredCODATAEinsteinCouplingCandidateAvailable =
  Einstein.gAuthorityMetadataPresent
    Einstein.canonicalEinsteinPhysicalCouplingCandidate

exactSpeedOfLightIsNotCalibrationBlocker : Bool
exactSpeedOfLightIsNotCalibrationBlocker = true

newEinsteinCouplingConventionRequired : Bool
newEinsteinCouplingConventionRequired = false

acceptedMeasuredGAuthorityStillRequired : Bool
acceptedMeasuredGAuthorityStillRequired =
  GAuthority.acceptedMeasuredGAuthorityStillRequired

sourceStressLengthSquaredScaleStillRequired : Bool
sourceStressLengthSquaredScaleStillRequired = true

separateStressAndLengthIdentificationRequired : Bool
separateStressAndLengthIdentificationRequired = false

physicalEinsteinCouplingAlreadyPromoted : Bool
physicalEinsteinCouplingAlreadyPromoted =
  GAuthority.acceptedPhysicalEinsteinCouplingAvailable

globalCandidatePromotionFlagStillFalse : Bool
globalCandidatePromotionFlagStillFalse =
  Einstein.physicalEinsteinCouplingPromoted
    Einstein.canonicalEinsteinPhysicalCouplingCandidate

exactNewtonianGClaimed : Bool
exactNewtonianGClaimed = GAuthority.exactNewtonianGClaimed

record AntigravitySICalibrationFrontier : Set where
  constructor antigravity-si-calibration-frontier
  field
    vendoredCandidatePresent : Bool
    exactCOpen : Bool
    newConventionOpen : Bool
    acceptedMeasuredGOpen : Bool
    stressLengthSquaredProductOpen : Bool
    separateStressScaleOpen : Bool
    separateLengthScaleOpen : Bool
    physicalKappaAlreadyPromoted : Bool
    globalCandidateFlagMutated : Bool
    exactGClaimed : Bool

canonicalAntigravitySICalibrationFrontier : AntigravitySICalibrationFrontier
canonicalAntigravitySICalibrationFrontier =
  antigravity-si-calibration-frontier
    true false false false true false false true false false

acceptedMeasuredGAuthorityStillRequiredIsFalse :
  acceptedMeasuredGAuthorityStillRequired ≡ false
acceptedMeasuredGAuthorityStillRequiredIsFalse =
  GAuthority.acceptedMeasuredGAuthorityStillRequiredIsFalse

newEinsteinCouplingConventionRequiredIsFalse :
  newEinsteinCouplingConventionRequired ≡ false
newEinsteinCouplingConventionRequiredIsFalse = refl

separateStressAndLengthIdentificationRequiredIsFalse :
  separateStressAndLengthIdentificationRequired ≡ false
separateStressAndLengthIdentificationRequiredIsFalse = refl

exactNewtonianGClaimedIsFalse : exactNewtonianGClaimed ≡ false
exactNewtonianGClaimedIsFalse = GAuthority.exactNewtonianGClaimedIsFalse
