{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkPotentialCouplingBenchmarkExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History
import DASHI.Quantum.QuantumBirthmarkFiniteHistoryTwoVacuumBenchmarkExact as Coupling

------------------------------------------------------------------------
-- FINITE HISTORY-ACTION -> VACUUM-POTENTIAL BENCHMARK
------------------------------------------------------------------------

historyActionGap : Nat
historyActionGap = 2

historyActionGapIsTwo : historyActionGap ≡ 2
historyActionGapIsTwo = refl

lowHistoryAction :
  History.historyAction History.historyABC ≡ 2
lowHistoryAction = refl

highHistoryAction :
  History.historyAction History.historyACB ≡ 4
highHistoryAction = refl

lowHistoryVacuumEnergy :
  Coupling.historyVacuumEnergy History.historyABC ≡ Int.+ 21 / 64
lowHistoryVacuumEnergy = Coupling.historyABCEnergy

highHistoryVacuumEnergy :
  Coupling.historyVacuumEnergy History.historyACB ≡ Int.+ 3 / 8
highHistoryVacuumEnergy = Coupling.historyACBEnergy

vacuumEnergyGap : ℚ
vacuumEnergyGap =
  Coupling.historyVacuumEnergy History.historyACB
  - Coupling.historyVacuumEnergy History.historyABC

vacuumEnergyGapIsThreeSixtyFourths :
  vacuumEnergyGap ≡ Int.+ 3 / 64
vacuumEnergyGapIsThreeSixtyFourths = solve []

actionGapSelectsDifferentVacuumEnergies : Bool
actionGapSelectsDifferentVacuumEnergies = true

finitePotentialCouplingBenchmarkOwned : Bool
finitePotentialCouplingBenchmarkOwned = true

sourceNativeCMP119CouplingStillRequired : Bool
sourceNativeCMP119CouplingStillRequired = true

finiteClassifierIsNotUniqueMicroscopicLaw : Bool
finiteClassifierIsNotUniqueMicroscopicLaw = true
