{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravitySICalibrationDonorMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.EinsteinPhysicalCouplingCalibrationExact as Einstein

------------------------------------------------------------------------
-- SI / PHYSICAL CALIBRATION DONOR MAX-CUT
--
-- Current master already owns a deterministic replay candidate for
--
--   kappa = 8*pi*G/c^4
--
-- in the energy-density convention, backed by a vendored CODATA-2022/NIST
-- artifact and checksum.  Exact c and the convention are therefore not the
-- remaining antigravity calibration problem.
--
-- The two genuine physical leaves are:
--   1. accepted measured-G authority/value ingestion with uncertainty;
--   2. the source-native physical stress*length^2 scale seen by the Kottler
--      consumer.
--
-- Separate identification of stress scale and length scale is stronger than
-- the consumer needs and is not scheduled as an independent payment.
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
acceptedMeasuredGAuthorityStillRequired = true

sourceStressLengthSquaredScaleStillRequired : Bool
sourceStressLengthSquaredScaleStillRequired = true

separateStressAndLengthIdentificationRequired : Bool
separateStressAndLengthIdentificationRequired = false

physicalEinsteinCouplingAlreadyPromoted : Bool
physicalEinsteinCouplingAlreadyPromoted =
  Einstein.physicalEinsteinCouplingPromoted
    Einstein.canonicalEinsteinPhysicalCouplingCandidate

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

canonicalAntigravitySICalibrationFrontier : AntigravitySICalibrationFrontier
canonicalAntigravitySICalibrationFrontier =
  antigravity-si-calibration-frontier
    true false false true true false false false

newEinsteinCouplingConventionRequiredIsFalse :
  newEinsteinCouplingConventionRequired ≡ false
newEinsteinCouplingConventionRequiredIsFalse = refl

separateStressAndLengthIdentificationRequiredIsFalse :
  separateStressAndLengthIdentificationRequired ≡ false
separateStressAndLengthIdentificationRequiredIsFalse = refl
