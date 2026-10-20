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

-- Structural status ledger. "Paid" here means the proof-relevant generic
-- interface/compiler exists in-repo. Empirical/source acquisition is tracked
-- separately by Diffraction3DImagingAcquisitionMaxCutExact so this layer does
-- not become stale as public Berkeley datasets and comparator experiments are
-- acquired.
record Diffraction3DImagingPhysicalMaxCut : Set where
  field
    propagationPaid : Bool
    physicalWeldPaid : Bool
    restrictedStabilityPaid : Bool
    detectorChannelPaid : Bool
    informationDesignPaid : Bool
    matchedPhotonComparatorPaid : Bool

open Diffraction3DImagingPhysicalMaxCut public

currentDiffraction3DImagingPhysicalMaxCut : Diffraction3DImagingPhysicalMaxCut
currentDiffraction3DImagingPhysicalMaxCut = record
  { propagationPaid = true
  ; physicalWeldPaid = true
  ; restrictedStabilityPaid = true
  ; detectorChannelPaid = true
  ; informationDesignPaid = true
  ; matchedPhotonComparatorPaid = true
  }

-- Remaining work is therefore not another structural optics abstraction.
-- Concrete acquisition/numerics live in Diffraction3DImagingAcquisitionMaxCutExact:
-- public PSF materialisation, same-H translated-column stability, calibrated
-- detector comparison, and any optional FZP arm.
