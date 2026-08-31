module DASHI.Cognition.PNF.LandscapeFluxOrderBridgeExact where

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.PNF.DecisionLandscapeFluxExact as Landscape
import DASHI.Cognition.PNF.NoncommutativeDecisionUpdateQQExact as Order

------------------------------------------------------------------------
-- LANDSCAPE + FLUX + NONCOMMUTATIVE HISTORY
--
-- A scalar potential can remain fixed while path-ordered state updates end at
-- different fine states.  This is the exact obstruction to treating a
-- potential landscape as the complete dynamics.
------------------------------------------------------------------------

record LandscapeHistoryState : Set where
  constructor landscapeHistoryState
  field
    landscapeState : Landscape.LandscapeState
    beliefState : Order.BeliefState

open LandscapeHistoryState public

initial : LandscapeHistoryState
initial = landscapeHistoryState Landscape.leftMinimum Order.initial

updateA : LandscapeHistoryState → LandscapeHistoryState
updateA state =
  landscapeHistoryState (landscapeState state) (Order.updateA (beliefState state))

updateB : LandscapeHistoryState → LandscapeHistoryState
updateB state =
  landscapeHistoryState (landscapeState state) (Order.updateB (beliefState state))

AB : LandscapeHistoryState
AB = updateB (updateA initial)

BA : LandscapeHistoryState
BA = updateA (updateB initial)

potentialObservation : LandscapeHistoryState → Nat
potentialObservation state = Landscape.potential (landscapeState state)

orderedEndpointsSharePotential : potentialObservation AB ≡ potentialObservation BA
orderedEndpointsSharePotential = refl

orderedEndpointsDiffer : AB ≡ BA → ⊥
orderedEndpointsDiffer equality =
  Order.updateMapsDoNotCommute (cong beliefState equality)

potentialCannotRecoverOrderedHistory :
  NF.FactorsThrough potentialObservation beliefState → ⊥
potentialCannotRecoverOrderedHistory =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness AB BA refl Order.updateMapsDoNotCommute)

samePotentialNoncommutingHistory :
  potentialObservation AB ≡ potentialObservation BA
  × (beliefState AB ≡ beliefState BA → ⊥)
samePotentialNoncommutingHistory = refl , Order.updateMapsDoNotCommute
