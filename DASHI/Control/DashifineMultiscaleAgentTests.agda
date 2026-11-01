module DASHI.Control.DashifineMultiscaleAgentTests where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (neg; zer; pos)
open import DASHI.Control.DashifineMultiscaleAgent

------------------------------------------------------------------------
-- Direction superposition and conflict preservation
------------------------------------------------------------------------

buyEvidence : DirectionEvidence
buyEvidence = directionEvidence false true

sellEvidence : DirectionEvidence
sellEvidence = directionEvidence true false

conflictedEvidence : DirectionEvidence
conflictedEvidence = directionEvidence true true

buyCollapsesPositive : collapseDirection buyEvidence ≡ pos
buyCollapsesPositive = refl

sellCollapsesNegative : collapseDirection sellEvidence ≡ neg
sellCollapsesNegative = refl

conflictDoesNotVote : collapseDirection conflictedEvidence ≡ zer
conflictDoesNotVote = refl

conflictIsObservable : conflictMask conflictedEvidence ≡ true
conflictIsObservable = refl

------------------------------------------------------------------------
-- The finite actionability quotient and its vertical PQN representation
------------------------------------------------------------------------

identityValuation : ActionabilityValuation ActionabilityBand
identityValuation =
  record
    { _refines_ = _≤band_
    ; valuation = λ a → a
    ; refinementMonotone = λ p → p
    }

pqnLowWitness : encodePQN low ≡ pqn false false true
pqnLowWitness = refl

pqnMiddleWitness : encodePQN middle ≡ pqn false true true
pqnMiddleWitness = refl

pqnHighWitness : encodePQN high ≡ pqn true true true
pqnHighWitness = refl

pqnRoundTrip : (a : ActionabilityBand) → decodePQN (encodePQN a) ≡ a
pqnRoundTrip = decodeEncodePQN

------------------------------------------------------------------------
-- Exact hysteresis graph witnesses
------------------------------------------------------------------------

holdDoesNotEnterAtMiddle : stepControl middle pos HOLD ≡ HOLD
holdDoesNotEnterAtMiddle = refl

buyPersistsAtMiddle : stepControl middle neg BUY ≡ BUY
buyPersistsAtMiddle = refl

sellPersistsAtMiddle : stepControl middle pos SELL ≡ SELL
sellPersistsAtMiddle = refl

lowExitsBuy : stepControl low pos BUY ≡ HOLD
lowExitsBuy = refl

highFlipsBuyToSell : stepControl high neg BUY ≡ SELL
highFlipsBuyToSell = refl

highFlipsSellToBuy : stepControl high pos SELL ≡ BUY
highFlipsSellToBuy = refl

------------------------------------------------------------------------
-- Multiscale bottleneck and closure witnesses
------------------------------------------------------------------------

fastBuy : ScaleCell
fastBuy = scaleCell buyEvidence high

slowBuy : ScaleCell
slowBuy = scaleCell buyEvidence high

uncertainBuy : ScaleCell
uncertainBuy = scaleCell buyEvidence middle

slowSell : ScaleCell
slowSell = scaleCell sellEvidence high

alignedScalesActBuy : closeCell (combineCells fastBuy slowBuy) HOLD ≡ BUY
alignedScalesActBuy = refl

middleBottleneckPreventsEntry :
  closeCell (combineCells fastBuy uncertainBuy) HOLD ≡ HOLD
middleBottleneckPreventsEntry = refl

opposedScalesRemainUnresolved :
  closeCell (combineCells fastBuy slowSell) HOLD ≡ HOLD
opposedScalesRemainUnresolved = refl

bottleneckWitness :
  actionability (combineCells fastBuy uncertainBuy) ≡ middle
bottleneckWitness = refl
