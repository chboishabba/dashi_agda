module DASHI.Culture.MissingDeceasedTwentyScientistPublicProducerExecutionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact as B
import DASHI.Physics.SpaceWeather.ZhangXiaoxinForecastProducerExecutionReadinessExact as Z

data ProducerExecutionBindingState : Set where
  manifestReadyUnexecuted : ProducerExecutionBindingState
  payloadParsedUnexecuted : ProducerExecutionBindingState
  sourceProducerExecuted : ProducerExecutionBindingState
  paperOutputsCompared : ProducerExecutionBindingState

record ProducerExecutionBinding : Set where
  constructor producer-execution-binding
  field
    person : String
    fibre : B.ScientistTechnologyFibre
    state : ProducerExecutionBindingState
    readiness : Z.ZhangProducerExecutionReadiness
    forwardCapability : String
    reverseObligation : String

open ProducerExecutionBinding public

zhangProducerExecutionBinding : ProducerExecutionBinding
zhangProducerExecutionBinding = producer-execution-binding
  "Zhang Xiaoxin"
  B.zhangXiaoxinFibre
  manifestReadyUnexecuted
  Z.zhangProducerExecutionReadiness
  "public CEEMDAN-CWT forecast producer with source data/code identifiers and finite manifest"
  "download -> hash check -> MAT schema parse -> code/dependency inspection -> execute -> compare source outputs"

producerExecutionBindings : List ProducerExecutionBinding
producerExecutionBindings = zhangProducerExecutionBinding ∷ []

producerExecutionBindingsCount : Nat
producerExecutionBindingsCount = 1

producerExecutionBindingPaysHistoricalUse : Bool
producerExecutionBindingPaysHistoricalUse = false

producerExecutionBindingPaysCustody : Bool
producerExecutionBindingPaysCustody = false

producerExecutionBindingPaysOperationalValidation : Bool
producerExecutionBindingPaysOperationalValidation = false

reverseExecutionObligationIsFirstClass : Bool
reverseExecutionObligationIsFirstClass = true
