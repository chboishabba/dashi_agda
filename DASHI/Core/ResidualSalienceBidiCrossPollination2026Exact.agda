module DASHI.Core.ResidualSalienceBidiCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster196830RegularBulkResidualControlPatternExact as MonsterResidual
import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop

record ConsumerDiscriminator (State : Set) : Set₁ where
  constructor consumer-discriminator
  field Answer : Set
        answer : State → Answer
        consumerReference : String
open ConsumerDiscriminator public

record ResidualSeparates {State : Set} (d : ConsumerDiscriminator State) : Set where
  constructor residual-separates
  field left right : State
        answersDiffer : answer d left ≢ answer d right
        witnessReference : String
open ResidualSeparates public

record ResidualSearchPriority : Set where
  constructor residual-search-priority
  field residualLive : Bool
        residualLiveIsTrue : residualLive ≡ true
        consumerRelevant : Bool
        consumerRelevantIsTrue : consumerRelevant ≡ true
        nextProbeReference priorityReading : String
open ResidualSearchPriority public

data ToyState : Set where bulkA bulkB residualLeft residualRight : ToyState
data ToyAnswer : Set where noSignal leftSignal rightSignal : ToyAnswer

toyAnswer : ToyState → ToyAnswer
toyAnswer bulkA = noSignal
toyAnswer bulkB = noSignal
toyAnswer residualLeft = leftSignal
toyAnswer residualRight = rightSignal

toyDiscriminator : ConsumerDiscriminator ToyState
toyDiscriminator = consumer-discriminator ToyAnswer toyAnswer "synthetic residual-salience consumer"

toyResidualSeparates : ResidualSeparates toyDiscriminator
toyResidualSeparates = residual-separates residualLeft residualRight (λ ()) "residual separates consumer"

data ResidualCardinalityDeterminesInformationValue : Set where
data MonsterResidualPatternTransfersMonsterAction : Set where

residualCardinalityDoesNotDetermineInformationValue : ResidualCardinalityDeterminesInformationValue → ⊥
residualCardinalityDoesNotDetermineInformationValue ()
monsterPatternDoesNotTransferMonsterAction : MonsterResidualPatternTransfersMonsterAction → ⊥
monsterPatternDoesNotTransferMonsterAction ()

record ResidualSalienceBoundary : Set where
  constructor residual-salience-boundary
  field cardinalityDistinctFromConsumerInformation residualMayControlNextProbe regularBulkMayRemainCompressed sourceActionNotTransferred : Bool

canonicalResidualSalienceBoundary : ResidualSalienceBoundary
canonicalResidualSalienceBoundary = residual-salience-boundary true true true true
