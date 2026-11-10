module DASHI.Chemistry.HydrogenPowerStationDispatchDecisionExact where

-- Priority: maximise actual energy SERVICE, not just methane tonnes.
-- Attribution: classical conservation/linear allocation economics, NIST HHV
-- and DASHI's earlier SI and solar/methane modules retain original owners.
-- User-defined PV + hydrocarbon station architecture; user-directed
-- ChatGPT-authored conditional mathematical implementation (2026-11-10).
-- IEA Global Hydrogen Review 2024: synthetic fuels introduce supply chain
-- losses and CO2 source matters; no physical output/price is invented.
--
-- NOTE: marginal comparison assumes divisible output at a FIXED same-time
-- demand value, no reserve requirement, no ramping, no storage degradation,
-- no minimum plant turndown and no already saturated electricity network.
-- Explicit dynamic dispatch remains an empirical/operational residual.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.Physics.Units.SI as SI
import DASHI.Chemistry.HydrogenSolarCarbonEnergyOptimizationExact as Energy
import DASHI.Chemistry.HydrogenFuelCycleTwoApplicationsExact as Deploy

-- All utility numbers are on the SAME valued-service scale;
-- electricity delivered at different times may have different value.
record CompetingSolarUses : Set where
  field
    directGridUsefulUnitsPerSolarUnit : Nat
    methaneUsefulUnitsPerMethaneMole : Nat
    solarUnitsPerMethaneMole : Nat
    methaneOpportunityExceedsDirect :
      directGridUsefulUnitsPerSolarUnit * solarUnitsPerMethaneMole
        ≤ methaneUsefulUnitsPerMethaneMole
open CompetingSolarUses public

-- A unit of solar energy spent on one methane molecule would otherwise
-- create n units of directly usable grid service. A source-paid storage
-- advantage can reverse the comparison; the theorem never says methane
-- intrinsically beats direct electrical conversion.
syntheticOutputAtLeastForegoneDirect :
  (d : CompetingSolarUses) →
  directGridUsefulUnitsPerSolarUnit d * solarUnitsPerMethaneMole d
    ≤ methaneUsefulUnitsPerMethaneMole d
syntheticOutputAtLeastForegoneDirect d =
  methaneOpportunityExceedsDirect d

-- Conversely if the direct service value exceeds methane service value,
-- no optimal *linear* plan sends flexible PV electricity to synthesis while
-- direct-use demand remains unserved. Such a comparison excludes mandatory
-- fuel-storage and grid-congestion constraints unless priced in both sides.
record DirectUseDominates : Set where
  field
    directUsefulUnitsPerSolarUnit : Nat
    syntheticUsefulUnitsPerMole : Nat
    solarCostPerMole : Nat
    dominates :
      syntheticUsefulUnitsPerMole
        ≤ directUsefulUnitsPerSolarUnit * solarCostPerMole
open DirectUseDominates public

-- A 100%-thermoneutral H2 electrolyser plus ideal Sabatier step yields
-- exactly 890350/(4*285830) of the original chemical HHV, BEFORE any
-- methane-to-electric generation. Unlike a source-measured generator η,
-- this is exact equality of *reported NIST numeric conventions*.
referenceMethaneInputJ : Nat
referenceMethaneInputJ = Energy.methaneThermoneutralElectricityJ

referenceMethaneHHVJ : Nat
referenceMethaneHHVJ = Energy.methaneHHVJ

thermoneutralReferenceSeparation :
  referenceMethaneHHVJ + Energy.sabatierCondensedHeatJ
    ≡ referenceMethaneInputJ
thermoneutralReferenceSeparation = refl

-- Entire power-station emission and carbon-source duty remain external;
-- PV electricity going into methane is unavailable for direct export.
record DispatchPhysicalReceipt : Set₁ where
  field
    co2Source : Deploy.CarbonOrigin
    solarPowerMeter : SI.Measurement SI.Energy SI.unitScale
    directGridDeliverabilityAndTimeValue : Set
    syntheticFuelStoreAndTimeValue : Set
    generatorActuallyCompatibleWithFuel : Set
    captureElectrolysisMethanationAndCompressionPower : Set
    annualCarbonAndWaterBalance : Set
    carbonIntensityAndDisplacedFossilBaseline : Set
    intermittentDispatchAndGridConstraints : Set
    independentlyCalibratedEnergyService : Set
