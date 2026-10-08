module DASHI.Physics.Optics.Diffraction3DImagingPhysicalMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Optics.DiffuserImagingObserverDynamicRangeExact
import DASHI.Physics.Optics.DiffuserNoiseStableRecoveryExact
import DASHI.Foundations.HyperformObserverFactorisationExact
import DASHI.Physics.Optics.FresnelZonePlateDiffuserCodecBridgeExact
import DASHI.Physics.Optics.FresnelAngularSpectrumPropagationExact
import DASHI.Physics.Optics.DiffuserPhysicalForwardWeldExact
import DASHI.Physics.Optics.DiffuserRestrictedStabilityProducerExact
import DASHI.Physics.Optics.PhotonDetectorChannelExact
import DASHI.Physics.Optics.DiffuserInformationDesignExact
import DASHI.Physics.Optics.MatchedPhotonImagerComparatorExact

-- Exact status ledger.  "Paid" here means the proof-relevant interface/compiler
-- exists in-repo.  The final three empirical/numerical leaves remain false:
-- actual Berkeley/Waller calibration, a measured/derived restricted kappa on
-- that same H, and a matched-photon experimental comparison.
record Diffraction3DImagingPhysicalMaxCut : Set where
  field
    propagationPaid : Bool
    physicalWeldPaid : Bool
    restrictedStabilityPaid : Bool
    detectorChannelPaid : Bool
    informationDesignPaid : Bool
    matchedPhotonComparatorPaid : Bool
    berkeleyCalibrationPaid : Bool
    measuredRestrictedKappaPaid : Bool
    matchedPhotonExperimentPaid : Bool

open Diffraction3DImagingPhysicalMaxCut public

currentDiffraction3DImagingPhysicalMaxCut : Diffraction3DImagingPhysicalMaxCut
currentDiffraction3DImagingPhysicalMaxCut = record
  { propagationPaid = true
  ; physicalWeldPaid = true
  ; restrictedStabilityPaid = true
  ; detectorChannelPaid = true
  ; informationDesignPaid = true
  ; matchedPhotonComparatorPaid = true
  ; berkeleyCalibrationPaid = false
  ; measuredRestrictedKappaPaid = false
  ; matchedPhotonExperimentPaid = false
  }

-- The remaining max-cut is intentionally physical, not representational:
--  1. populate the physical weld from actual depth-indexed calibrated PSFs;
--  2. populate RestrictedInverseBudget.restrictedStability for that same H;
--  3. populate the detector statistics and matched-photon comparator from
--     measured instrument parameters/data.
