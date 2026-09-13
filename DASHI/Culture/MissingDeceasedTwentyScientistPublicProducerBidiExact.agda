module DASHI.Culture.MissingDeceasedTwentyScientistPublicProducerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact as B
import DASHI.Physics.SpaceWeather.ZhangXiaoxinForecastPublicProducerExact as Z

data PublicProducerState : Set where
  publicDataAndCodeLocatedUnexecuted : PublicProducerState
  publicProducerExecuted : PublicProducerState
  operationallyValidated : PublicProducerState

record PublicProducerBinding : Set where
  constructor public-producer-binding
  field
    person : String
    fibre : B.ScientistTechnologyFibre
    state : PublicProducerState
    dataDOI : String
    codeDOI : String
    producerReceipt : Z.ZhangPublicProducerReceipt
    newlyPaid : String
    stillUnpaid : String

open PublicProducerBinding public

zhangPublicProducerBinding : PublicProducerBinding
zhangPublicProducerBinding = public-producer-binding
  "Zhang Xiaoxin"
  B.zhangXiaoxinFibre
  publicDataAndCodeLocatedUnexecuted
  "10.5281/zenodo.8093239"
  "10.5281/zenodo.8093257"
  Z.zhangPublicProducerReceipt
  "publisher-linked public processed-data deposit, public code deposit, Data Set S1 and three exact MAT file manifests"
  "download/parse MAT payloads; inspect code-file manifest; execute producer; compare event-level outputs and paper aggregate metrics"

publicProducerBindings : List PublicProducerBinding
publicProducerBindings = zhangPublicProducerBinding ∷ []

publicProducerBindingsCount : Nat
publicProducerBindingsCount = 1

publicDepositDoesNotEqualExecutedProducer : Bool
publicDepositDoesNotEqualExecutedProducer = false

publicProducerDoesNotPayHistoricalDeployment : Bool
publicProducerDoesNotPayHistoricalDeployment = false

publicProducerDoesNotPayCustody : Bool
publicProducerDoesNotPayCustody = false

publicProducerCanRefineExecutionPareto : Bool
publicProducerCanRefineExecutionPareto = true
