module DASHI.Physics.SpaceWeather.ZhangXiaoxinForecastProducerExecutionReadinessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.SpaceWeather.ZhangXiaoxinForecastPublicProducerExact as Public

------------------------------------------------------------------------
-- PUBLIC PRODUCER -> EXECUTION READINESS
--
-- This owner records only what is required before a source producer can be
-- rerun.  Publicly located files, sizes and hashes are not themselves an
-- execution receipt.  Parsing, code inspection, dependency closure and rerun
-- remain separate typed stages.
------------------------------------------------------------------------

data ProducerExecutionStage : Set where
  publicManifestLocated : ProducerExecutionStage
  payloadIntegrityReady : ProducerExecutionStage
  payloadParsed : ProducerExecutionStage
  codeInspected : ProducerExecutionStage
  dependencyClosed : ProducerExecutionStage
  producerExecuted : ProducerExecutionStage
  paperOutputsCompared : ProducerExecutionStage

record ZhangProducerExecutionReadiness : Set where
  constructor zhang-producer-execution-readiness
  field
    paperDOI : String
    processedDataDOI : String
    codeDOI : String
    dataFileCount : Nat
    dataManifest : String
    integrityManifest : String
    stationAndCadence : String
    decisionRule : String
    currentStage : ProducerExecutionStage
    hashesAvailable : Bool
    payloadDownloadedByDASHI : Bool
    payloadHashesCheckedByDASHI : Bool
    payloadParsedByDASHI : Bool
    codeManifestInspectedByDASHI : Bool
    dependenciesClosedByDASHI : Bool
    producerExecutedByDASHI : Bool
    eventOutputsComparedByDASHI : Bool
    nextExecutionLeaf : String

open ZhangProducerExecutionReadiness public

zhangProducerExecutionReadiness : ZhangProducerExecutionReadiness
zhangProducerExecutionReadiness = zhang-producer-execution-readiness
  Public.paperDOI Public.processedDataDOI Public.codeDOI
  3
  "data_initial_v30.mat; output_v30.mat; predicted_table_v30.mat"
  "three source-published MD5 values retained by ZhangXiaoxinForecastPublicProducerExact"
  "Oulu neutron monitor; 1998-2019; 30 min cadence"
  "precursor threshold = 1.2 times base value; reported mean lead time = 50.4 h"
  publicManifestLocated
  true
  false false false false false false false
  "download source deposits; verify hashes; inspect MAT schemas and code manifest; close MATLAB/toolbox dependencies; execute; compare event-level outputs and published aggregates"

publicManifestAgreesWithPriorOwner : Bool
publicManifestAgreesWithPriorOwner = true

producerLocatedDoesNotMeanProducerExecuted : Bool
producerLocatedDoesNotMeanProducerExecuted = false

hashAvailableDoesNotMeanHashVerifiedByDASHI : Bool
hashAvailableDoesNotMeanHashVerifiedByDASHI = false

publicDataDoesNotMeanParsedPayload : Bool
publicDataDoesNotMeanParsedPayload = false

publicCodeDepositDoesNotMeanDependenciesClosed : Bool
publicCodeDepositDoesNotMeanDependenciesClosed = false

executionDoesNotPayOperationalForecastValidation : Bool
executionDoesNotPayOperationalForecastValidation = false
