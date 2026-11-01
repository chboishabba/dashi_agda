module DASHI.Culture.MissingDeceasedTwentyScientistMaterializationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact as B
import DASHI.Physics.SpaceWeather.ZhangXiaoxinForecastMaterializationExact as Z

data MaterializationState : Set where
  remoteManifestOnly : MaterializationState
  localBytesPresent : MaterializationState
  hashesVerified : MaterializationState
  payloadParsed : MaterializationState
  producerExecuted : MaterializationState

record MaterializationBinding : Set where
  constructor materialization-binding
  field
    person : String
    fibre : B.ScientistTechnologyFibre
    state : MaterializationState
    witness : Z.ZhangForecastMaterialization
    forwardCapability : String
    reverseObligation : String

open MaterializationBinding public

zhangMaterializationBinding : MaterializationBinding
zhangMaterializationBinding = materialization-binding
  "Zhang Xiaoxin"
  B.zhangXiaoxinFibre
  remoteManifestOnly
  Z.zhangForecastMaterialization
  "public forecast producer with exact source data/code deposits and integrity metadata"
  "obtain local bytes -> verify source hashes -> parse MAT/code -> close dependencies -> execute -> compare outputs"

materializationBindings : List MaterializationBinding
materializationBindings = zhangMaterializationBinding ∷ []

materializationBindingsCount : Nat
materializationBindingsCount = 1

materializationPaysExecution : Bool
materializationPaysExecution = false

materializationPaysHistoricalDeployment : Bool
materializationPaysHistoricalDeployment = false

materializationPaysCustody : Bool
materializationPaysCustody = false
