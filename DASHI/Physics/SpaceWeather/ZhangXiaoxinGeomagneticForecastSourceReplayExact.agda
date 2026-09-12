module DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastSourceReplayExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastBidiExact as Z

------------------------------------------------------------------------
-- SOURCE-EXACT REPLAY COORDINATES
-- DOI 10.1029/2023SW003522.
-- Publisher full text reports 229 CME-driven events from 1998-2019 at Oulu:
-- 166 with Kp >= 5 and 63 with Kp < 5; among the 166 storm events, 129 were
-- accurately predicted (77.7% recall). CEEMDAN reconstruction uses IMF4+IMF5,
-- and CME-related reconstructed-spectrum variation is concentrated at 4-24 h.
------------------------------------------------------------------------

record ZhangForecastSourceReplay : Set where
  constructor zhang-forecast-source-replay
  field
    sourceReference : String
    station : String
    interval : String
    totalCMEEvents : Nat
    kpAtLeast5Events : Nat
    kpBelow5Events : Nat
    analysedStormEvents : Nat
    accuratelyPredictedEvents : Nat
    reportedRecall : String
    selectedIMFs : String
    sourceBackedTimeScale : String
    method : String
    exactHyperparameterReplayPaid : Bool
    operationalForecastThresholdPaid : Bool

open ZhangForecastSourceReplay public

sourceExactZhangForecastReplay : ZhangForecastSourceReplay
sourceExactZhangForecastReplay = zhang-forecast-source-replay
  "DOI 10.1029/2023SW003522"
  "Oulu cosmic-ray station"
  "1998-2019; solar cycles 23 and 24"
  229
  166
  63
  166
  129
  "77.7%"
  "IMF4 + IMF5 selected after CEEMDAN decomposition"
  "CME-related reconstructed-spectrum variation mainly between 4 and 24 h"
  "spectral whitening followed by CEEMDAN-CWT precursor extraction"
  false
  false

existingPipeline : Z.GeomagneticForecastPipeline
existingPipeline = Z.canonicalZhangXiaoxinForecastPipeline

sourceReplayPaysSyntheticEventCountsReplacement : Bool
sourceReplayPaysSyntheticEventCountsReplacement = true

sourceReplayPaysExactIMFSelection : Bool
sourceReplayPaysExactIMFSelection = true

sourceReplayPaysOperationalThreshold : Bool
sourceReplayPaysOperationalThreshold = false

sourceReplayPaysFengyunPayloadCalibration : Bool
sourceReplayPaysFengyunPayloadCalibration = false
