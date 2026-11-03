{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkFiniteHistoryTwoVacuumBenchmarkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Physics.Foundations.FiniteHistoryFunctionalExact as History
import DASHI.Quantum.QuantumBirthmarkTwoPhaseHistoryModelExact as Phase

------------------------------------------------------------------------
-- FINITE HISTORY -> TWO-VACUUM BENCHMARK
--
-- The existing finite-history owner has two admissible histories beginning at
-- the same initial configuration but with different complete-history actions:
--   ABC -> 2, ACB -> 4.
-- We use that distinction as a finite phase classifier into the already-owned
-- two-vacuum history model.
------------------------------------------------------------------------

historyPhase : History.History3 → Phase.HistoryPhase
historyPhase (History.configurationA ,
  (History.configurationB , History.configurationC)) = Phase.lowHistoryPhase
historyPhase (History.configurationA ,
  (History.configurationC , History.configurationB)) = Phase.highHistoryPhase
historyPhase history = Phase.lowHistoryPhase

historyVacuumEnergy : History.History3 → ℚ
historyVacuumEnergy history =
  Phase.historyPhaseEnergy (historyPhase history)

historyABCSelectsLowVacuum :
  historyPhase History.historyABC ≡ Phase.lowHistoryPhase
historyABCSelectsLowVacuum = refl

historyACBSelectsHighVacuum :
  historyPhase History.historyACB ≡ Phase.highHistoryPhase
historyACBSelectsHighVacuum = refl

historyABCEnergy :
  historyVacuumEnergy History.historyABC ≡ Int.+ 21 / 64
historyABCEnergy = Phase.lowHistoryEnergy

historyACBEnergy :
  historyVacuumEnergy History.historyACB ≡ Int.+ 3 / 8
historyACBEnergy = Phase.highHistoryEnergy

sameInitialStateDifferentHistoryActionReused :
  History.historyAction History.historyABC ≡ 2
  × History.historyAction History.historyACB ≡ 4
sameInitialStateDifferentHistoryActionReused =
  History.sameInitialStateDifferentAction

finiteHistoryCanSelectDifferentVacuumPhase : Bool
finiteHistoryCanSelectDifferentVacuumPhase = true

sameInitialConfigurationDoesNotFixHistoryVacuumInBenchmark : Bool
sameInitialConfigurationDoesNotFixHistoryVacuumInBenchmark = true

classifierDerivedFromQuantumBirthmarkDynamics : Bool
classifierDerivedFromQuantumBirthmarkDynamics = false

benchmarkIsCosmologicalPrediction : Bool
benchmarkIsCosmologicalPrediction = false
