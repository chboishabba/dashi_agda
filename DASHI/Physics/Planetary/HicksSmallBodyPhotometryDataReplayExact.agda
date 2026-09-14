module DASHI.Physics.Planetary.HicksSmallBodyPhotometryDataReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Planetary.HicksSmallBodyPhotometrySourceReplayExact as Source

------------------------------------------------------------------------
-- HICKS / 3122 FLORENCE SOURCE-DATA REPLAY
--
-- The currently paid public carrier supplies campaign identity, Hicks's Table
-- Mountain participation, observation date and the campaign-level 2.4 h
-- rotation estimate.  It does not publish the Hicks lightcurve array here.
------------------------------------------------------------------------

record HicksPhotometryDataReplay : Set where
  constructor hicks-photometry-data-replay
  field
    sourceReference : String
    target : String
    observatory : String
    observationDate : String
    campaignRotationPeriodTenthsHour : Nat
    independentRadarConsistency : Bool
    hicksRawLightcurveArrayPaid : Bool
    hicksViewingGeometryPaid : Bool
    hicksPhotometricCalibrationPaid : Bool
    campaignPeriodSolelyHicksDerived : Bool

open HicksPhotometryDataReplay public

hicksPhotometryDataReplay : HicksPhotometryDataReplay
hicksPhotometryDataReplay = hicks-photometry-data-replay
  "NASA/JPL CNEOS, 2017-09-11, Telescopes Worldwide Collaborate to Observe Asteroid Florence"
  "3122 Florence"
  "NASA Table Mountain Observatory, Wrightwood, California"
  "2017-08-30"
  24
  true
  false
  false
  false
  false

existingSourceReplay : Source.HicksPhotometryReplay
existingSourceReplay = Source.hicksPhotometryReplay

sourceDataReplayPaysCampaignPeriodCoordinate : Bool
sourceDataReplayPaysCampaignPeriodCoordinate = true

sourceDataReplayPaysRawHicksLightcurve : Bool
sourceDataReplayPaysRawHicksLightcurve = false

sourceDataReplayPaysUniqueThreeDimensionalShape : Bool
sourceDataReplayPaysUniqueThreeDimensionalShape = false
