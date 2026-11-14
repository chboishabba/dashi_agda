module DASHI.Chemistry.HydrogenFuelCycleExact where

-- Source lineage / provenance (2026-11-09):
-- * Conventional water electrolysis, methane Sabatier synthesis,
--   and methane combustion chemistry: established chemical prior art;
--   these equations are not attributed to Michael McLaren.
-- * Generic stoichiometric theorem owner:
--   DASHI.Analysis.StoichiometricConservation.
-- * Generic open-system energy owner:
--   DASHI.Chemistry.IndustrialReactiveEnergyBalanceExact.
-- * Engineering scenario was described by the user from public McLaren/XFuel
--   material; this DASHI/ChatGPT-assisted construction is a *conditional model*.
-- * Patent inventorship, title, reactor identity, numerical conversion
--   efficiencies and physical performance require independent receipts.
-- * Source-written / static proof, NOT kernel-verified in this commit.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Chemistry.IndustrialReactiveEnergyBalanceExact as Ledger

-- Exact atom accounting for the *selected* C/H/O reaction system.
-- The atoms are counted, not the molecules. This is independent of the
-- reaction yield and says nothing about whether a reactor actually works.
record CHO : Set where
  constructor cho
  field
    carbon : Nat
    hydrogen : Nat
    oxygen : Nat

open CHO public

record SameCHO (before after : CHO) : Set where
  field
    sameCarbon : carbon before ≡ carbon after
    sameHydrogen : hydrogen before ≡ hydrogen after
    sameOxygen : oxygen before ≡ oxygen after

-- 2 H2O -> 2 H2 + O2.
waterElectrolysisInput : CHO
waterElectrolysisInput = cho 0 (2 * 2) (2 * 1)

waterElectrolysisOutput : CHO
waterElectrolysisOutput = cho 0 (2 * 2) (1 * 2)

waterElectrolysisAtoms : SameCHO waterElectrolysisInput waterElectrolysisOutput
waterElectrolysisAtoms = record
  { sameCarbon = refl ; sameHydrogen = refl ; sameOxygen = refl }

-- CO2 + 4 H2 -> CH4 + 2 H2O.
sabatierInput : CHO
sabatierInput = cho 1 (4 * 2) (1 * 2)

sabatierOutput : CHO
sabatierOutput = cho 1 ((1 * 4) + (2 * 2)) (2 * 1)

sabatierAtoms : SameCHO sabatierInput sabatierOutput
sabatierAtoms = record
  { sameCarbon = refl ; sameHydrogen = refl ; sameOxygen = refl }

-- CH4 + 2 O2 -> CO2 + 2 H2O.
methaneCombustionInput : CHO
methaneCombustionInput = cho 1 (1 * 4) (2 * 2)

methaneCombustionOutput : CHO
methaneCombustionOutput = cho 1 (2 * 2) ((1 * 2) + (2 * 1))

methaneCombustionAtoms :
  SameCHO methaneCombustionInput methaneCombustionOutput
methaneCombustionAtoms = record
  { sameCarbon = refl ; sameHydrogen = refl ; sameOxygen = refl }

-- Hydrogen production is partitioned ONCE among direct combustion,
-- synthesis, storage, and venting. A single hydrogen stream cannot
-- simultaneously support two independent fuel-substitution credits.
record HydrogenPartition : Set where
  field
    produced : Nat
    toEngine : Nat
    toSynthesis : Nat
    toStorage : Nat
    vented : Nat
    partition :
      produced ≡ (toEngine + toSynthesis) + (toStorage + vented)

open HydrogenPartition public

hydrogenAllocatedExactlyOnce :
  (p : HydrogenPartition) →
  produced p ≡ (toEngine p + toSynthesis p) +
               (toStorage p + vented p)
hydrogenAllocatedExactlyOnce = partition

-- A concrete exact example, with 10 units allocated to combustion,
-- 8 units allocated to synthesis, 2 stored and 0 vented.
samplePartition : HydrogenPartition
samplePartition = record
  { produced = 20 ; toEngine = 10 ; toSynthesis = 8
  ; toStorage = 2 ; vented = 0 ; partition = refl }

samplePartitionRegression :
  produced samplePartition ≡ 20
samplePartitionRegression = refl

-- Explicit separation of diesel fuel and combustible hydrogen energy.
-- The efficiency numerator is useful work. The denominator counts
-- *all* engine chemical energy, not just diesel.
record MatchedOutputCombustion : Set where
  field
    baselineDiesel : Nat
    assistedDiesel : Nat
    burnedHydrogen : Nat
    burnedSyntheticFuel : Nat
    baselineEfficiencyNumerator : Nat
    assistedEfficiencyNumerator : Nat
    commonEfficiencyDenominator : Nat

    matchedOutput :
      baselineEfficiencyNumerator * baselineDiesel
      ≡ assistedEfficiencyNumerator *
         (assistedDiesel + burnedHydrogen + burnedSyntheticFuel)

open MatchedOutputCombustion public

matchedEngineOutputIdentity :
  (s : MatchedOutputCombustion) →
  baselineEfficiencyNumerator s * baselineDiesel s
  ≡ assistedEfficiencyNumerator s *
      (assistedDiesel s + burnedHydrogen s + burnedSyntheticFuel s)
matchedEngineOutputIdentity = matchedOutput

-- Example: 35% baseline on 100 units, 50% assisted on 70 units.
-- This exhibits the arithmetic cost of a 30% diesel decrease without
-- H2 substitution. It is NOT evidence that any engine reaches 50%.
thirtyPercentWithoutSubstitution : MatchedOutputCombustion
thirtyPercentWithoutSubstitution = record
  { baselineDiesel = 100
  ; assistedDiesel = 70
  ; burnedHydrogen = 0
  ; burnedSyntheticFuel = 0
  ; baselineEfficiencyNumerator = 35
  ; assistedEfficiencyNumerator = 50
  ; commonEfficiencyDenominator = 100
  ; matchedOutput = refl
  }

thirtyPercentArithmeticRegression :
  35 * 100 ≡ 50 * (70 + 0 + 0)
thirtyPercentArithmeticRegression =
  matchedOutput thirtyPercentWithoutSubstitution

-- No false conflation of hydrogen-as-fuel with a catalytic reagent
-- regenerated after the process: the H2 intake is a consumed input.
data CombustionRole : Set where
  consumedHydrogenFuel : CombustionRole
  regeneratedCatalyst : CombustionRole

hydrogenFuelIsNotRegeneratedCatalyst :
  consumedHydrogenFuel ≡ regeneratedCatalyst → ⊥
hydrogenFuelIsNotRegeneratedCatalyst ()

-- Distinct applications may use different equipment. A patent disclosure
-- alone cannot select the physically installed apparatus.
record DeviceBoundary : Set where
  field
    selectedMode : Ledger.DeviceMode
    auxiliaries : Ledger.DeviceAuxiliaries
    sameMode : selectedMode ≡ Ledger.mode auxiliaries

open DeviceBoundary public
