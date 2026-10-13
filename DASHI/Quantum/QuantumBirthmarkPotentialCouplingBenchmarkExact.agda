{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkPotentialCouplingBenchmarkExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History
import DASHI.Quantum.QuantumBirthmarkFiniteHistoryTwoVacuumBenchmarkExact as Coupling

------------------------------------------------------------------------
-- FINITE HISTORY-ACTION -> VACUUM-POTENTIAL BENCHMARK
--
-- Existing source-independent finite history data already give two admissible
-- histories with the same initial configuration and actions 2 and 4.  The
-- branch's explicit classifier maps them to the exact two stable vacuum levels.
-- This closes a constructive coupling benchmark; it does not derive the
-- classifier from CMP119/YM source dynamics.
------------------------------------------------------------------------

historyActionGap : Nat
historyActionGap =
  History.historyAction History.historyACB

lowHistoryAction :
  History.historyAction History.historyABC ≡ 2
lowHistoryAction = History.sameInitialStateDifferentAction .proj₁

highHistoryAction :
  History.historyAction History.historyACB ≡ 4
highHistoryAction = History.sameInitialStateDifferentAction .proj₂

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
