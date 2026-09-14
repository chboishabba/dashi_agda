module DASHI.Physics.SpaceWeather.ZhangXiaoxinForecastMaterializationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.SpaceWeather.ZhangXiaoxinForecastProducerExecutionReadinessExact as R

record ZhangForecastMaterialization : Set where
  constructor zhang-forecast-materialization
  field
    sourceDataDOI : String
    sourceCodeDOI : String
    declaredDataFiles : Nat
    declaredManifest : String
    declaredIntegrityReceipt : String
    payloadDownloadedByDASHI : Bool
    payloadHashesCheckedByDASHI : Bool
    payloadParsedByDASHI : Bool
    codeDownloadedByDASHI : Bool
    codeManifestInspectedByDASHI : Bool
    sourceProducerExecutedByDASHI : Bool
    nextMaterializationLeaf : String

open ZhangForecastMaterialization public

zhangForecastMaterialization : ZhangForecastMaterialization
zhangForecastMaterialization = zhang-forecast-materialization
  "10.5281/zenodo.8093239"
  "10.5281/zenodo.8093257"
  3
  "data_initial_v30.mat; output_v30.mat; predicted_table_v30.mat"
  "source MD5 values retained by ZhangXiaoxinForecastPublicProducerExact"
  false false false false false false
  "materialize source deposits into an executable workspace; verify published hashes; inspect MAT schemas and code manifest; record dependency closure; execute and compare event-level outputs"

priorReadiness : R.ZhangProducerExecutionReadiness
priorReadiness = R.zhangProducerExecutionReadiness

remoteManifestLocated : Bool
remoteManifestLocated = true

remoteManifestDoesNotMeanLocalMaterialization : Bool
remoteManifestDoesNotMeanLocalMaterialization = false

materializationDoesNotMeanParsing : Bool
materializationDoesNotMeanParsing = false

parsingDoesNotMeanExecution : Bool
parsingDoesNotMeanExecution = false
