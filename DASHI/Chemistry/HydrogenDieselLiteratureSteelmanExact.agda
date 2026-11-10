module DASHI.Chemistry.HydrogenDieselLiteratureSteelmanExact where

-- Attribution and scientific/authority boundary (2026-11-10):
-- (1) Amatnieks, Smigins, Skrzek, Matijošius and Birkavs (2026),
--     Energies 19(17),3951, DOI 10.3390/en19173951:
--     published, engine-specific pressure/combustion timing changes.
-- (2) Estrada, Moreno, Gonzalez-Quiroga, Bula and Duarte-Forero (2022),
--     Heliyon 8(4) e09285, DOI 10.1016/j.heliyon.2022.e09285:
--     20 L/min H2, 13.45 V, 15.1 A cell parameters in Table 3,
--     0.0899 kg/m3 H2 density, 119.7 MJ/kg H2 LHV, BFC vs BTE equations.
-- (3) Single-zone heat-release first law derives from established engine
--     thermodynamics (Heywood/Gatowski), not a McLaren patent.
-- (4) User-directed DASHI integration; ChatGPT-authored exact numerical
--     identity regressions. Literature measurements belong to the
--     respective authors. No published numbers are McLaren observations.
--
-- Positive reported maxima vary across operating points; treating them
-- as simultaneous measurements is unsupported. A pressure-rise-rate
-- increase is NOT automatically an efficiency improvement.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record PublishedObservation : Set where
  constructor published
  field
    sourceDOI : String
    physicalSystem : String
    loadAndSpeedScope : String
    observation : String
    limitation : String
open PublishedObservation public

pressureLiterature : PublishedObservation
pressureLiterature = published
  "10.3390/en19173951"
  "AVL 5402 common rail; H2 inlet addition"
  "1200, 1500, 2000, 2500 rpm; 5 to 25 Nm; modes differ"
  "peak pressure up to +20%; pressure-rise rate up to +56%; CA50 up to 3.5 degrees earlier at selected point"
  "not one simultaneous observation; not a generic gain factor for another engine"

combustionDurationLiterature : PublishedObservation
combustionDurationLiterature = published
  "10.3390/en19173951"
  "AVL 5402 common rail; H2 inlet addition"
  "multiple separately selected operating points"
  "combustion duration can grow up to +46%; low loads can reduce peak cylinder pressure"
  "hydrogen effect non-monotone and engine/load dependent"

electrolyserLiterature : PublishedObservation
electrolyserLiterature = published
  "10.1016/j.heliyon.2022.e09285"
  "296 cm3 20:1 single-cylinder diesel generator, separately described alkaline cell"
  "Table 3 cell and Table 5 fuel/flow properties"
  "reported 20 L/min H2, 13.45 V, 15.1 A; 119.7 MJ/kg LHV and .0899 kg/m3 H2"
  "reported cells/flow not reconciled to AC supply, gas tank inventory or same time window"

-- At the nominal values in Estrada et al.'s reported tables:
-- P_DC=13.45*15.1=203.095 W.
-- P_H2,LHV=(20 L/min)*(0.0899 kg/m3)*(119.7 MJ/kg)
--             * (1 m3/1000 L)*(1 min/60 s) = 3587.01 W.
-- Values here are milliwatt integers; these are DERIVED comparisons.
reportedDCMilliWatt : Nat
reportedDCMilliWatt = 203095

reportedHydrogenLHVMilliWatt : Nat
reportedHydrogenLHVMilliWatt = 3587010

sourceNominalEnergyGap :
  reportedDCMilliWatt + 3383915 ≡ reportedHydrogenLHVMilliWatt
sourceNominalEnergyGap = refl

-- This disparity is a source-reconciliation flag; not an established
-- apparatus violation. The AC feed, storage, actual flow and voltage/current
-- integration window must be independently matched before claiming eta.

-- The 30%-diesel steelman WITH hydrogen at 10% of engine fuel energy:
-- baseline diesel 90 units and baseline efficiency 35% -> 31.5 output;
-- assisted diesel 63 and hydrogen 7 =70 units at 45% -> 31.5 output.
-- Hypothetical electrolyser 70%: 10 units electricity produces 7 H2.
-- Therefore diesel reduction is 27/90 =30%; all-external-input reduction
-- is (90-(63+10))/90=17/90 =18.89% before other auxiliary burdens.
-- These are exact rational normalisations, not measured efficiency ratios.

matchedUsefulOutputScenario :
  35 * 90 ≡ 45 * (63 + 7)
matchedUsefulOutputScenario = refl

assumedElectrolyserScenario :
  7 * 100 ≡ 70 * 10
assumedElectrolyserScenario = refl

dieselThirtyPercentScenario :
  63 + 27 ≡ 90
dieselThirtyPercentScenario = refl

netInputSavingScenario :
  (63 + 10) + 17 ≡ 90
netInputSavingScenario = refl

-- A second scenario: 30% diesel saving with only 1 energy unit H2.
-- Engine efficiency 35/71 (~49.3%) is required at 35 units of work.
-- This is physically admissible arithmetic, not a verified achievable
-- pressure-timing response from any source.
oneUnitHydrogenThreshold :
  35 * (70 + 1) ≡ 71 * 35
oneUnitHydrogenThreshold = refl

-- The checked algebra cannot identify actual engine pressure trace,
-- combustion kinetics, pollutant output, brake efficiency, or apparatus IP.
