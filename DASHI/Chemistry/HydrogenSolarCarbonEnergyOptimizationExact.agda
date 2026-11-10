module DASHI.Chemistry.HydrogenSolarCarbonEnergyOptimizationExact where

-- Attribution (2026-11-10):
-- BIPM SI, original DASHI Atomic369, NIST source-attributed standard water
-- formation and methane HHV, and Sabatier/H2-water electrolysis reactions
-- retain their respective scientific and formal authorship. User requested
-- the solar-power-station and externally charged car idealisation, and
-- ChatGPT authored this derived source/energy decision framework.
--
-- Boundary: reference-state thermoneutral electrolysis (electricity alone)
-- versus reversible electrolysis (electricity plus externally paid heat).
-- This file is conditional algebra, not an independently measured plant,
-- operating catalyst yield, or patent invention proof.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.Chemistry.HydrogenFuelCycleNISTThermochemistryExact as NIST
import DASHI.Chemistry.HydrogenSolarCarbonGeneralStoichiometryExact as Stoich
import DASHI.Physics.Units.SI as SI

h2HHVJ : Nat
h2HHVJ = NIST.magnitudeJPerMole NIST.nistHydrogenHHV

methaneHHVJ : Nat
methaneHHVJ = NIST.magnitudeJPerMole NIST.nistMethaneHHV

sabatierCondensedHeatJ : Nat
sabatierCondensedHeatJ = 252970

-- This is an exact arithmetic equation between REPORTED NUMBERS.
-- The underlying standard-state enthalpy values carry literature
-- uncertainty; it is not an exact physical process enthalpy.
methaneHydrogenEnergyBalance :
  (n : Nat) →
  (n * methaneHHVJ) + (n * sabatierCondensedHeatJ)
    ≡ (n * 4) * h2HHVJ
methaneHydrogenEnergyBalance n =
  solve 1
    (λ n →
      (n :* con 890350) :+ (n :* con 252970)
        := (n :* con 4) :* con 285830)
    refl n

-- Source values at standard 298.15 K:
-- reversible electricity ~=237.13 kJ H2/mol plus ~=48.70 kJ/mol heat;
-- thermoneutral electricity alone ~=285.83 kJ/mol. Heat is not free.
reversibleElectricalJPerH2 : Nat
reversibleElectricalJPerH2 = 237130

heatJPerH2 : Nat
heatJPerH2 = 48700

reversibleAndHeatMakesHHV :
  reversibleElectricalJPerH2 + heatJPerH2 ≡ h2HHVJ
reversibleAndHeatMakesHHV = refl

-- For each mole CH4, 4 H2 need 4*285830 J thermoneutral electricity,
-- or 4*237130 J reversible electricity PLUS 4*48700 J compatible heat.
methaneReversibleElectricityJ : Nat
methaneReversibleElectricityJ = 4 * reversibleElectricalJPerH2

methaneRequiredHeatJ : Nat
methaneRequiredHeatJ = 4 * heatJPerH2

methaneThermoneutralElectricityJ : Nat
methaneThermoneutralElectricityJ = 4 * h2HHVJ

splitReversibleAndThermoneutral :
  methaneReversibleElectricityJ + methaneRequiredHeatJ
    ≡ methaneThermoneutralElectricityJ
splitReversibleAndThermoneutral = refl

-- Theoretical Sabatier release in the condensed-water enthalpy
-- convention is greater than the thermal fraction of reversible
-- water electrolysis; temperature/heat-exchanger compatibility and
-- condensation state still determine whether it can actually supply it.
heatReleaseCoversReversibleDemandNumerically :
  methaneRequiredHeatJ + 58170 ≡ sabatierCondensedHeatJ
heatReleaseCoversReversibleDemandNumerically = refl

-- Finite resource feasibility via cross-multiplied caps, avoiding
-- rounding-based false precision. No implicit unlimited carbon, sunlight,
-- tank water, product selectivity or catalyst is introduced.
record AdmittedSolarMethaneAllocation : Set where
  field
    productMoles : Nat
    capturedCarbonMoles : Nat
    availableGrossWaterMoles : Nat
    availableElectricityJoules : Nat
    additionalCaptureAndAuxiliaryJoules : Nat
    carbonBound : productMoles ≤ capturedCarbonMoles
    waterBound : 4 * productMoles ≤ availableGrossWaterMoles
    electricityBound :
      methaneThermoneutralElectricityJ * productMoles
        + additionalCaptureAndAuxiliaryJoules
      ≤ availableElectricityJoules

open AdmittedSolarMethaneAllocation public

-- Positive carbon/solar allocation is not the same as net cost,
-- environmental or primary-fuel benefit. This cross-check keeps the
-- non-energy carbon objective separate from electrical efficiency.
record ActualFossilDisplacementReceipt : Set₁ where
  field
    allocation : AdmittedSolarMethaneAllocation
    hydrocarbonsActuallySynthesisedAndAssayed : Set
    stationCanUseSelectedFuel : Set
    sourceSpecificSolarResource : SI.Measurement SI.Energy SI.unitScale
    carbonOriginAndLifecycleBaseline : Set
    sameOutputVirginFuelDisplacement : Set
    timeMatchedHeatAndAuxiliaryInputs : Set
    unconvertedCarbonAndStorageAccounted : Set
    pollutantAndLifecycleEmissionsAudit : Set

-- Critical optimisation result for the *same* engine-useful-work efficiency:
-- 4 H2 carry nominally 1,143,320 J HHV, while 1 CH4 carries 890,350 J.
-- Converting hydrogen to methane sacrifices some chemical exergy;
-- methane may nonetheless be the useful stored/transportable fuel.
-- This arithmetic does not compare engine compatibility or mass storage.
