module DASHI.Physics.SpaceWeather.ZhangXiaoxinForecastAlgorithmProducerDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record ZhangForecastProducerDepth : Set where
  constructor zhang-forecast-producer-depth
  field
    sourceReference : String
    spectralWhiteningStageVisible : Bool
    ceemdanEquationVisible : Bool
    cwtEquationVisible : Bool
    imfSelectionVisible : Bool
    eventAggregateCountsVisible : Bool
    eventLevelRowsVisible : Bool
    exactHyperparametersVisible : Bool
    runnableReferenceCodeVisible : Bool
    nextProducerLeaf : String

open ZhangForecastProducerDepth public

zhangForecastProducerDepth : ZhangForecastProducerDepth
zhangForecastProducerDepth = zhang-forecast-producer-depth
  "DOI 10.1029/2023SW003522"
  true
  true
  true
  true
  true
  false
  false
  false
  "recover event-level table plus exact SWM/CEEMDAN/CWT parameterisation and implementation code"

visibleEquationsPayAlgorithmTopology : Bool
visibleEquationsPayAlgorithmTopology = true

algorithmTopologyPaysEventReplay : Bool
algorithmTopologyPaysEventReplay = false

algorithmTopologyPaysOperationalForecast : Bool
algorithmTopologyPaysOperationalForecast = false
