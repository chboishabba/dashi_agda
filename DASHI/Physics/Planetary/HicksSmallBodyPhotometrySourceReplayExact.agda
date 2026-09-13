module DASHI.Physics.Planetary.HicksSmallBodyPhotometrySourceReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Planetary.HicksSmallBodyPhotometryBidiExact as Base

record HicksPhotometryReplay : Set where
  constructor hicks-photometry-replay
  field
    sourceReference : String
    target : String
    hicksObservatory : String
    hicksObservationDate : String
    campaignRotationPeriodTenthsHour : Nat
    rotationInferenceSource : String
    radarIndependentConsistency : Bool
    exactHicksLightcurveArrayPaid : Bool
    exactViewingGeometryPaid : Bool
    exactPhotometricCalibrationPaid : Bool

open HicksPhotometryReplay public

hicksPhotometryReplay : HicksPhotometryReplay
hicksPhotometryReplay = hicks-photometry-replay
  "NASA/JPL CNEOS, 2017-09-11, Telescopes Worldwide Collaborate to Observe Asteroid Florence"
  "3122 Florence"
  "NASA Table Mountain Observatory, Wrightwood, California"
  "2017-08-30"
  24
  "multi-observer optical lightcurves including Michael Hicks; campaign estimate 2.4 h"
  true
  false false false

existingBoundary : Base.SmallBodyInferenceBoundary
existingBoundary = Base.canonicalSmallBodyInferenceBoundary

campaignReceiptPaysHicksParticipation : Bool
campaignReceiptPaysHicksParticipation = true

campaignPeriodIsSolelyHicksDerived : Bool
campaignPeriodIsSolelyHicksDerived = false

campaignPeriodPaysThreeDimensionalShapeWithoutRadar : Bool
campaignPeriodPaysThreeDimensionalShapeWithoutRadar = false
