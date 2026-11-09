module DASHI.Chemistry.HydrogenCombustionIdentifiabilityExact where

-- Attribution (2026-11-09):
-- Thermodynamic efficiency and equal-output accounting are established
-- engineering definitions, not an invention by Michael McLaren.
-- This under-identification counterexample is a user-directed, ChatGPT-
-- drafted formal test; it does not assert that either device exists.
-- No patent, vendor statement or arithmetic fixture is laboratory evidence.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Chemistry.HydrogenEfficiencyCrossMultiplyExact as Model

-- Exact signed-free rational efficiency representation:
-- eta = numerator/denominator and useful output = workNumerator
-- in the model's common energy units.  No actual efficiency is asserted.
record SameDieselObserved : Set where
  field
    baselineFuel : Nat
    assistedDiesel : Nat
    injectedHydrogen : Nat
    assistedEfficiencyNumerator : Nat
    assistedEfficiencyDenominator : Nat
    deliveredWork : Nat
    sameUsefulOutput :
      assistedEfficiencyNumerator *
        (assistedDiesel + injectedHydrogen)
        ≡ deliveredWork * assistedEfficiencyDenominator

open SameDieselObserved public

-- Candidate 1: 70 diesel, zero H2, useful work 35.
-- 50% engine efficiency is *hypothetical*, not measured.
combustionOnlyCandidate : SameDieselObserved
combustionOnlyCandidate = record
  { baselineFuel = 100
  ; assistedDiesel = 70
  ; injectedHydrogen = 0
  ; assistedEfficiencyNumerator = 1
  ; assistedEfficiencyDenominator = 2
  ; deliveredWork = 35
  ; sameUsefulOutput = refl
  }

-- Candidate 2: same 70 diesel, 10 H2, useful work 35;
-- 7/16 = 43.75% physical engine efficiency.
hydrogenSubstitutionCandidate : SameDieselObserved
hydrogenSubstitutionCandidate = record
  { baselineFuel = 100
  ; assistedDiesel = 70
  ; injectedHydrogen = 10
  ; assistedEfficiencyNumerator = 7
  ; assistedEfficiencyDenominator = 16
  ; deliveredWork = 35
  ; sameUsefulOutput = refl
  }

sameObservedDiesel :
  assistedDiesel combustionOnlyCandidate
    ≡ assistedDiesel hydrogenSubstitutionCandidate
sameObservedDiesel = refl

sameObservedOutput :
  deliveredWork combustionOnlyCandidate
    ≡ deliveredWork hydrogenSubstitutionCandidate
sameObservedOutput = refl

distinctHydrogenRequirements :
  injectedHydrogen combustionOnlyCandidate
    ≡ injectedHydrogen hydrogenSubstitutionCandidate → ⊥
distinctHydrogenRequirements ()

-- Hence diesel input plus useful output does NOT by itself identify
-- whether hydrogen heat input or combustion efficiency changed.
-- Separately metering hydrogen and obtaining a genuine independent
-- engine-efficiency measurement is a necessary identification seam.

-- Additional exact 30%-diesel-reduction case:
-- energy quantities in half-kWh units, 200 baseline diesel at 35% gives
-- 70 units output; assisted 140 diesel + 21 H2 = 161 chemical input,
-- so achieving 70 output requires eta=70/161.
thirtyPercentWithFifteenKWhElectricity : SameDieselObserved
thirtyPercentWithFifteenKWhElectricity = record
  { baselineFuel = 200
  ; assistedDiesel = 140
  ; injectedHydrogen = 21
  ; assistedEfficiencyNumerator = 70
  ; assistedEfficiencyDenominator = 161
  ; deliveredWork = 70
  ; sameUsefulOutput = refl
  }

-- The hydrogen input 21 half-kWh units = 10.5 kWh; if independently
-- made at assumed 70% HHV electrolysis efficiency this needs 15 kWh.
-- The arithmetic does not identify a real device or its auxiliary loads.
