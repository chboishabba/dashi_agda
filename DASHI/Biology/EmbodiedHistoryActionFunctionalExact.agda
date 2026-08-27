module DASHI.Biology.EmbodiedHistoryActionFunctionalExact where

open import DASHI.Core.Prelude

import DASHI.Biology.TwoBoundaryHyperformalismExact as Two

------------------------------------------------------------------------
-- TRAJECTORY COST/ACTION LIVES ON HISTORIES, NOT ONLY ENDPOINT STATES.
--
-- This is a finite structural analogue of an action functional.  No Boltzmann,
-- path-integral, least-action, or biological optimality law is asserted.
------------------------------------------------------------------------

data RouteLabel : Set where
  threatRoute safeRoute : RouteLabel

record HistoryCost : Set where
  constructor historyCost
  field
    effort : Nat
    delayedStress : Nat
    barrierCost : Nat
    optionalityLoss : Nat

open HistoryCost public

costFor : RouteLabel → HistoryCost
costFor threatRoute = historyCost 1 3 3 3
costFor safeRoute = historyCost 2 1 1 1

totalCost : HistoryCost → Nat
totalCost cost =
  effort cost + delayedStress cost + barrierCost cost + optionalityLoss cost

sameEndpointThreatPath : Two.Reach Two.startCell Two.goalCell
sameEndpointThreatPath = Two.threatPath

sameEndpointSafePath : Two.Reach Two.startCell Two.goalCell
sameEndpointSafePath = Two.safePath

sameBoundariesDifferentRouteCost :
  totalCost (costFor threatRoute) ≡ totalCost (costFor safeRoute) → ⊥
sameBoundariesDifferentRouteCost ()

record HistoryActionBoundary : Set where
  constructor historyActionBoundary
  field
    endpointDeterminesTrajectoryCost : Bool
    instantaneousUtilityIsOnlyPossibleDecisionObject : Bool
    finiteCostImpliesBoltzmannWeight : Bool
    sameEndpointCanHideDifferentPathCost : Bool

canonicalHistoryActionBoundary : HistoryActionBoundary
canonicalHistoryActionBoundary =
  historyActionBoundary false false false true
