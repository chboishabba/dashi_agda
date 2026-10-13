{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkTwoPhaseHistoryModelExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_)

import DASHI.Physics.Foundations.GRQFTTwoVacuumAmplitudePotentialExact as Potential

------------------------------------------------------------------------
-- MINIMAL TWO-PHASE HISTORY ORDER PARAMETER
--
-- This is the smallest explicit model that stops saying "introduce a scalar by
-- hand" without pretending the scalar has already been derived microscopically.
-- The history sector has two coarse phases and a selected order-parameter map
-- into the already-constructed two-vacuum potential.
------------------------------------------------------------------------

data HistoryPhase : Set where
  lowHistoryPhase : HistoryPhase
  highHistoryPhase : HistoryPhase

historyOrderParameter : HistoryPhase → ℚ
historyOrderParameter lowHistoryPhase = Potential.interiorVacuumField
historyOrderParameter highHistoryPhase = Potential.exteriorVacuumField

historyPhaseEnergy : HistoryPhase → ℚ
historyPhaseEnergy phase = Potential.vacuumPotential (historyOrderParameter phase)

lowHistoryEnergy :
  historyPhaseEnergy lowHistoryPhase ≡ Int.+ 21 / 64
lowHistoryEnergy = Potential.interiorVacuumEnergy

highHistoryEnergy :
  historyPhaseEnergy highHistoryPhase ≡ Int.+ 3 / 8
highHistoryEnergy = Potential.exteriorVacuumEnergy

lowHistoryPhaseStationary :
  Potential.vacuumPotentialPrime (historyOrderParameter lowHistoryPhase) ≡ 0ℚ
lowHistoryPhaseStationary = Potential.interiorStationary

highHistoryPhaseStationary :
  Potential.vacuumPotentialPrime (historyOrderParameter highHistoryPhase) ≡ 0ℚ
highHistoryPhaseStationary = Potential.exteriorStationary

record TwoPhaseHistoryModelBoundary : Set where
  constructor two-phase-history-model-boundary
  field
    historyOrderParameterExplicit : Bool
    bothHistoryPhasesMappedToStableVacua : Bool
    exactVacuumAmplitudesProduced : Bool
    arbitraryQuintessencePotentialStillNeeded : Bool
    microscopicBirthmarkStatisticsSelectHistoryPhase : Bool
    transitionRateDerivedFromBirthmarkDynamics : Bool

canonicalTwoPhaseHistoryModelBoundary : TwoPhaseHistoryModelBoundary
canonicalTwoPhaseHistoryModelBoundary =
  two-phase-history-model-boundary
    true true true false false false

twoPhaseHistoryOrderParameterModelOwned : Bool
twoPhaseHistoryOrderParameterModelOwned = true

microscopicPhaseSelectionStillRequired : Bool
microscopicPhaseSelectionStillRequired = true
