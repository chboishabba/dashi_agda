module DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastBidiExact as Zhang

------------------------------------------------------------------------
-- FINITE FORECAST-PIPELINE RECONSTRUCTION
--
-- The finite series below witnesses the stage topology only. It is not claimed
-- to reproduce the source paper's hidden data split, CEEMDAN settings, wavelet
-- scales, prediction coefficients or reported metrics.
------------------------------------------------------------------------

record FiniteZhangXiaoxinForecastWitness : Set where
  constructor finite-zhang-xiaoxin-forecast-witness
  field
    sourceReference : String
    inputSamples : List Nat
    stages : List Zhang.ForecastStage
    decompositionComponentCount : Nat
    waveletScaleCount : Nat
    finitePrediction : Nat
    finiteObservedValue : Nat
    syntheticReconstruction : Bool
    sourceMetricReproduced : Bool
    nextExactLeaf : String

open FiniteZhangXiaoxinForecastWitness public

finiteZhangXiaoxinForecastWitness : FiniteZhangXiaoxinForecastWitness
finiteZhangXiaoxinForecastWitness = finite-zhang-xiaoxin-forecast-witness
  "DOI 10.1029/2023SW003522"
  (12 ∷ 15 ∷ 14 ∷ 21 ∷ 18 ∷ 25 ∷ 23 ∷ 28 ∷ [])
  (Zhang.inputSeries ∷ Zhang.spectralWhitening ∷ Zhang.CEEMDANDecomposition ∷
   Zhang.waveletTransform ∷ Zhang.featureIntegration ∷ Zhang.prediction ∷ Zhang.validation ∷ [])
  3
  2
  26
  27
  true
  false
  "recover source input data, whitening/CEEMDAN/wavelet parameters, prediction rule and published validation metrics, then replace the synthetic finite carrier with a source-exact replay"

finitePipelineTouchesEveryPublishedStage : Bool
finitePipelineTouchesEveryPublishedStage = true

finiteWitnessIsSourceForecastReplication : Bool
finiteWitnessIsSourceForecastReplication = false

finiteWitnessPaysFengyunCalibration : Bool
finiteWitnessPaysFengyunCalibration = false
