{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkFiniteOrderParameterCouplingExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_)

import DASHI.Quantum.QuantumBirthmarkCommonHistoryIdentityBenchmarkExact as Birthmark
import DASHI.Quantum.QuantumBirthmarkFiniteHistoryTwoVacuumBenchmarkExact as HistoryPhase
import DASHI.Quantum.QuantumBirthmarkTwoPhaseHistoryModelExact as Phase

------------------------------------------------------------------------
-- FINITE BIRTHMARK -> HISTORY -> ORDER PARAMETER -> VACUUM ENERGY
------------------------------------------------------------------------

birthmarkPhase : Birthmark.BirthmarkClass → Phase.HistoryPhase
birthmarkPhase birthmark =
  HistoryPhase.historyPhase (Birthmark.selectedHistory birthmark)

birthmarkOrderParameter : Birthmark.BirthmarkClass → ℚ
birthmarkOrderParameter birthmark =
  Phase.historyOrderParameter (birthmarkPhase birthmark)

birthmarkVacuumEnergy : Birthmark.BirthmarkClass → ℚ
birthmarkVacuumEnergy birthmark =
  Phase.historyPhaseEnergy (birthmarkPhase birthmark)

lowBirthmarkOrderParameter :
  birthmarkOrderParameter Birthmark.lowBirthmark ≡ 0ℚ
lowBirthmarkOrderParameter = refl

highBirthmarkOrderParameter :
  birthmarkOrderParameter Birthmark.highBirthmark ≡ 1ℚ
highBirthmarkOrderParameter = refl

lowBirthmarkVacuumEnergy :
  birthmarkVacuumEnergy Birthmark.lowBirthmark ≡ Int.+ 21 / 64
lowBirthmarkVacuumEnergy = Phase.lowHistoryEnergy

highBirthmarkVacuumEnergy :
  birthmarkVacuumEnergy Birthmark.highBirthmark ≡ Int.+ 3 / 8
highBirthmarkVacuumEnergy = Phase.highHistoryEnergy

finiteBirthmarkToOrderParameterCouplingOwned : Bool
finiteBirthmarkToOrderParameterCouplingOwned = true

finiteBirthmarkToVacuumAmplitudeOwned : Bool
finiteBirthmarkToVacuumAmplitudeOwned = true

continuumBirthmarkStatisticsLawStillRequired : Bool
continuumBirthmarkStatisticsLawStillRequired = true

prxReturnEnhancementIdentifiedWithOrderParameter : Bool
prxReturnEnhancementIdentifiedWithOrderParameter = false

cosmologicalPotentialCouplingDerivedFromPRXData : Bool
cosmologicalPotentialCouplingDerivedFromPRXData = false
