module DASHI.Physics.Closure.W9PairTransportBridgeObstruction where

-- W9 theorem-interface bridge audit.
--
-- The current kill interface accepts either the existing pair-transport
-- pressure witness or the weighted replacement obligation.  The available
-- unary weighted-Qcore/Nat-bound story is not one of those constructors.
-- This module records the exact typed obstruction without constructing a
-- W9KillReceipt.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_,_)

import DASHI.Arithmetic.ArithmeticIntegerEmbedding as AIE
import DASHI.Arithmetic.WeightedValuationEnergy as WVE
import DASHI.Physics.Closure.BlockerKillConditions as Kill
import DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation as W9
import DASHI.Physics.Closure.DeltaToQuadraticBridgeTheorem as DQ

Canonical15PairPressureWitness : Setω
Canonical15PairPressureWitness =
  W9.ExistingCancellationPressureCompatibilityObligation
    W9.canonical15Theorem
    W9.canonical15Dimension

WeightedCancellationIdentification : Set
WeightedCancellationIdentification =
  ∀ input →
    + (AIE.deltaSum (WVE.left input) (WVE.right input))
    ≡
    + (WVE.weightedQuadraticEnergy (WVE.left input))

data W9PairTransportBridgeStatus : Set where
  blockedByPairTransportEqualityMismatch :
    W9PairTransportBridgeStatus
  blockedByWeightedReplacementIdentificationMismatch :
    W9PairTransportBridgeStatus
  requiresNewAcceptedKillRoute :
    W9PairTransportBridgeStatus

record W9PairTransportBridgeObstruction : Setω where
  field
    actualKillCondition :
      Kill.KillCondition

    actualKillConditionIsW9 :
      Kill.KillCondition.lane actualKillCondition
      ≡
      Kill.W9Cancellation

    actualKillConditionIsStillBlocked :
      Kill.KillCondition.currentState actualKillCondition
      ≡
      Kill.blocked

    existingRouteCounterexample :
      DQ.DeltaPair

    existingRouteImpossible :
      Canonical15PairPressureWitness → ⊥

    existingRouteCounterexampleMismatch :
      (+ (AIE.deltaSum W9.one W9.three))
      W9.≢
      (DQ.contractionEnergy
        W9.canonical15Theorem
        (DQ.canonicalDeltaTransport
          W9.canonical15Theorem
          W9.canonical15Dimension
          existingRouteCounterexample))

    weightedRouteCounterexample :
      DQ.WeightedInput

    weightedRouteImpossible :
      WeightedCancellationIdentification → ⊥

    weightedRouteCounterexampleMismatch :
      (+ (AIE.deltaSum
          (WVE.left weightedRouteCounterexample)
          (WVE.right weightedRouteCounterexample)))
      W9.≢
      (+ (WVE.weightedQuadraticEnergy
          (WVE.left weightedRouteCounterexample)))

    firstMissingBridge :
      String

    obstructionBoundary :
      List String

    status :
      W9PairTransportBridgeStatus

canonicalW9PairTransportBridgeObstruction :
  W9PairTransportBridgeObstruction
canonicalW9PairTransportBridgeObstruction =
  record
    { actualKillCondition =
        Kill.w9KillCondition
    ; actualKillConditionIsW9 =
        refl
    ; actualKillConditionIsStillBlocked =
        refl
    ; existingRouteCounterexample =
        W9.one , W9.three
    ; existingRouteImpossible =
        W9.canonical15ExistingPressureWitnessObstruction
    ; existingRouteCounterexampleMismatch =
        W9.canonical15PressureWitnessConcreteMismatch
    ; weightedRouteCounterexample =
        W9.CancellationToWeightedQuadraticIdentificationObstruction.counterexampleInput
          W9.canonicalCancellationToWeightedQuadraticIdentificationObstruction
    ; weightedRouteImpossible =
        W9.CancellationToWeightedQuadraticIdentificationObstruction.noUniformIdentification
          W9.canonicalCancellationToWeightedQuadraticIdentificationObstruction
    ; weightedRouteCounterexampleMismatch =
        W9.CancellationToWeightedQuadraticIdentificationObstruction.counterexampleMismatch
          W9.canonicalCancellationToWeightedQuadraticIdentificationObstruction
    ; firstMissingBridge =
        "Either prove ExistingCancellationPressureCompatibilityObligation.pressureWitness over canonicalDeltaTransport, prove WeightedValuationReplacementObligation.cancellationPressureIdentifiesWeightedQuadraticEnergy, or add a new accepted W9KillRouteReceipt constructor for the unary Nat bound"
    ; obstructionBoundary =
        "canonicalDeltaTransport theorem refl (x , y) uses the pair embeddedProfileCarrier"
        ∷ "ExistingCancellationPressureCompatibilityObligation requires a pointwise Z equality over that pair transport"
        ∷ "WeightedValuationReplacementObligation uses canonicalWeightedQuadraticTransport of the left input"
        ∷ "The current repo has counterexamples for both accepted routes"
        ∷ "No W9KillReceipt is constructed here"
        ∷ []
    ; status =
        requiresNewAcceptedKillRoute
    }

currentW9PairTransportBridgeStatus :
  W9PairTransportBridgeStatus
currentW9PairTransportBridgeStatus =
  W9PairTransportBridgeObstruction.status
    canonicalW9PairTransportBridgeObstruction
