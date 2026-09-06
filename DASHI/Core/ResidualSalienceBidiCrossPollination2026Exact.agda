module DASHI.Core.ResidualSalienceBidiCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster196830RegularBulkResidualControlPatternExact as MonsterResidual
import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop

------------------------------------------------------------------------
-- RESIDUAL SALIENCE -- BIDI CROSS-POLLINATION
--
-- Repository donors:
--   DASHI.Moonshine.Monster196830RegularBulkResidualControlPatternExact
--     (merged PR #697)
--   DASHI.Core.HistoryIndexedProofExperimentActionLoopExact
--     (merged PR #697)
--
-- DASHI extension: a small residual may be disproportionately informative for
-- the current consumer even when most of the carrier lies in a regular bulk.
-- No Monster cardinality, action or representation is transferred to the
-- generic carrier below.
------------------------------------------------------------------------

record BulkResidualSplit (State : Set) : Set₁ where
  constructor bulk-residual-split
  field
    Bulk Residual : Set
    classifyBulk : State → Bool
    bulkReference : String
    residualReference : String

open BulkResidualSplit public

record ConsumerDiscriminator (State : Set) : Set₁ where
  constructor consumer-discriminator
  field
    Answer : Set
    answer : State → Answer
    consumerReference : String

open ConsumerDiscriminator public

record ResidualSeparates
    {State : Set}
    (d : ConsumerDiscriminator State) : Set where
  constructor residual-separates
  field
    left right : State
    answersDiffer : answer d left ≢ answer d right
    witnessReference : String

open ResidualSeparates public

record ResidualSearchPriority : Set where
  constructor residual-search-priority
  field
    residualLive : Bool
    residualLiveIsTrue : residualLive ≡ true
    consumerRelevant : Bool
    consumerRelevantIsTrue : consumerRelevant ≡ true
    nextProbeReference : String
    priorityReading : String

open ResidualSearchPriority public

------------------------------------------------------------------------
-- Finite calibration: bulk size and residual size do not determine which
-- coordinate carries the consumer's discriminator.
------------------------------------------------------------------------

data ToyState : Set where
  bulkA bulkB residualLeft residualRight : ToyState

data ToyAnswer : Set where
  noSignal leftSignal rightSignal : ToyAnswer

toyAnswer : ToyState → ToyAnswer
toyAnswer bulkA = noSignal
toyAnswer bulkB = noSignal
toyAnswer residualLeft = leftSignal
toyAnswer residualRight = rightSignal

toyDiscriminator : ConsumerDiscriminator ToyState
toyDiscriminator = consumer-discriminator ToyAnswer toyAnswer
  "synthetic residual-salience consumer"

toyResidualSeparates : ResidualSeparates toyDiscriminator
toyResidualSeparates = residual-separates residualLeft residualRight (λ ())
  "two residual states separate the consumer while the regular bulk does not"

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data SmallResidualMeansUnimportant : Set where
data LargeBulkMeansConsumerComplete : Set where
data ResidualCardinalityDeterminesInformationValue : Set where
data MonsterResidualPatternTransfersMonsterAction : Set where

smallResidualDoesNotMeanUnimportant : SmallResidualMeansUnimportant → ⊥
smallResidualDoesNotMeanUnimportant ()

largeBulkDoesNotMeanConsumerComplete : LargeBulkMeansConsumerComplete → ⊥
largeBulkDoesNotMeanConsumerComplete ()

residualCardinalityDoesNotDetermineInformationValue :
  ResidualCardinalityDeterminesInformationValue → ⊥
residualCardinalityDoesNotDetermineInformationValue ()

monsterPatternDoesNotTransferMonsterAction :
  MonsterResidualPatternTransfersMonsterAction → ⊥
monsterPatternDoesNotTransferMonsterAction ()

record ResidualSalienceBoundary : Set where
  constructor residual-salience-boundary
  field
    cardinalityDistinctFromConsumerInformation : Bool
    residualMayControlNextProbe : Bool
    regularBulkMayRemainCompressed : Bool
    sourceActionNotTransferred : Bool

canonicalResidualSalienceBoundary : ResidualSalienceBoundary
canonicalResidualSalienceBoundary =
  residual-salience-boundary true true true true
