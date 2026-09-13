module DASHI.Physics.SpaceWeather.ZhangXiaoxinGeomagneticForecastBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificCapabilityCarrierBidiExact as C
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

------------------------------------------------------------------------
-- ZHANG XIAOXIN: NON-RECURRENT GEOMAGNETIC-STORM FORECAST PIPELINE
--
-- Source anchor: DOI 10.1029/2023SW003522.
-- The source-backed method combines spectral whitening with CEEMDAN-CWT.
-- This owner types the pipeline without inventing hidden hyperparameters or
-- treating forecast authorship as Fengyun payload-calibration possession.
------------------------------------------------------------------------

data ForecastStage : Set where
  inputSeries spectralWhitening CEEMDANDecomposition waveletTransform
  featureIntegration prediction validation : ForecastStage

record GeomagneticForecastPipeline : Set where
  constructor geomagnetic-forecast-pipeline
  field
    sourceReference : String
    targetPhenomenon : String
    stages : List ForecastStage
    sourceBackedMethod : String
    outputMeaning : String
    missingExecutableCoordinate : String

open GeomagneticForecastPipeline public

canonicalZhangXiaoxinForecastPipeline : GeomagneticForecastPipeline
canonicalZhangXiaoxinForecastPipeline = geomagnetic-forecast-pipeline
  "DOI 10.1029/2023SW003522"
  "CME-driven non-recurrent geomagnetic storms"
  (inputSeries ∷ spectralWhitening ∷ CEEMDANDecomposition ∷ waveletTransform ∷
   featureIntegration ∷ prediction ∷ validation ∷ [])
  "spectral whitening plus CEEMDAN-CWT prediction pipeline"
  "a forecast/estimate of geomagnetic-storm behaviour from the source-defined time-series inputs"
  "exact dataset split, preprocessing parameters, CEEMDAN settings, wavelet family/scales, prediction rule and evaluation metrics"

zhangForecastCarrier : C.ScientificCapabilityCarrier
zhangForecastCarrier = C.scientific-capability-carrier
  "space-weather prediction"
  "CEEMDAN-CWT forecasting algorithm and validation corpus"
  C.sourceCodeOrAlgorithm
  C.carrierPublic
  "spectral whitening plus decomposition/wavelet forecasting"
  "DOI 10.1029/2023SW003522"
  "Method identity is public; executable parameterisation and operational data/calibration state require additional source objects."

zhangForecastTransformation : T.ApplicationTransformation
zhangForecastTransformation = T.application-transformation
  "space-weather forecast and operational risk input"
  (T.governingPhysics ∷ T.sourceOrAlgorithmImplementation ∷ T.uncertaintyModel ∷ [])
  (T.validationCorpus ∷ T.operatingWindow ∷ T.integrationWorkflow ∷ [])
  "DOI 10.1029/2023SW003522"
  "Operational use requires source-exact data, forecast thresholds, validation metrics and mission-specific decision integration."

data ZhangForecastReverseTarget : Set where
  acquireInputDataset acquireWhiteningParameters acquireCEEMDANParameters
  acquireWaveletParameters acquirePredictionRule acquireValidationMetrics
  acquireOperationalThresholds acquireFengyunPayloadCalibration : ZhangForecastReverseTarget

forecastPipelineImpliesFengyunPayloadCalibration : Bool
forecastPipelineImpliesFengyunPayloadCalibration = false

posthumousPublicationImpliesPostLossActiveRole : Bool
posthumousPublicationImpliesPostLossActiveRole = false

forecastCanProvideMissionRiskInput : Bool
forecastCanProvideMissionRiskInput = true
