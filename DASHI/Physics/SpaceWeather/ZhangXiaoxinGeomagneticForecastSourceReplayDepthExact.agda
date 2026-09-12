module DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastSourceReplayDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastSourceReplayExact as Base

record ZhangForecastDepthReplay : Set where
  constructor zhang-forecast-depth-replay
  field
    sourceReference : String
    totalEvents : Nat
    stormEvents : Nat
    nonStormEvents : Nat
    correctlyPredictedStormEvents : Nat
    recallNumerator recallDenominator : Nat
    recallPercent : String
    station : String
    sourceInterval : String
    decompositionSelection : String
    precursorTimeScale : String
    exactCEEMDANParametersPaid : Bool
    exactCWTParametersPaid : Bool
    runnableSourceCodePaid : Bool

open ZhangForecastDepthReplay public

zhangForecastDepthReplay : ZhangForecastDepthReplay
zhangForecastDepthReplay = zhang-forecast-depth-replay
  "DOI 10.1029/2023SW003522"
  229 166 63 129 129 166 "77.7%"
  "Oulu cosmic-ray station"
  "1998-2019, solar cycles 23 and 24"
  "IMF4 + IMF5"
  "4-24 h"
  false false false

baseReplay : Base.ZhangForecastSourceReplay
baseReplay = Base.sourceExactZhangForecastReplay

reportedRecallHasFiniteCountWitness : Bool
reportedRecallHasFiniteCountWitness = true

finiteCountWitnessPaysOperationalThreshold : Bool
finiteCountWitnessPaysOperationalThreshold = false

publishedMethodNamePaysHyperparameters : Bool
publishedMethodNamePaysHyperparameters = false
