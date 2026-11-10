module DASHI.Chemistry.HydrogenSolarCarbonPublishedPilotExact where

-- Named, measured, third-party demonstration: Emanuele Moioli,
-- Patrick Senn, Simon Østrup, Christoph Hütter, "Results from the
-- operation of an efficient and flexible large-scale biogas methanation
-- system", Energy Advances 3 (2024), 131-142.
-- DOI: 10.1039/D3YA00436H; original scientific and apparatus attribution
-- stays with the authors and their employing organisations.
-- https://pubs.rsc.org/en/content/articlehtml/2024/ya/d3ya00436h
--
-- USER requested a solar co-located existing hydrocarbon station and
-- a separate offboard-battery car retrofit. This module integrates a
-- published analog; it DOES NOT identify a McLaren/XFuel apparatus
-- or attribute the pilot technology to that proponent or ChatGPT.
--
-- From the paper's Figure 6 / Table 3 (approximately kW):
-- electrolyser electricity 188, existing biogas chemical input 130,
-- other utilities 34, total energy input 352.
-- SNG chemical product ~248 kW, high-pressure steam useful heat ~19 kW.
-- Source definitions:
-- 248/352=70.45% "feed to biomethane".
-- (248+19)/352=75.85% "feed to products including steam".
-- Do NOT use 248/188 as a pure electricity-to-fuel efficiency: it
-- hides the 130 kW of original biogas chemical feed and 34 kW utilities.
-- The authors call the plant ~240-kW class and report 76% efficiency.
--
-- These are source-quoted/rounded numeric data, not exact measured
-- constants or externally reconstructed calibration/uncertainty.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Units.SI as SI

record PilotProvenance : Set where
  field
    originalAuthors : String
    originalDOI : String
    actualFeedstock : String
    reportedEnergyBasis : String
    completeMeterCalibrationAndRawData : Set

record PublishedBiogasPilotLedger : Set where
  field
    electrolysisElectricityKW : Nat
    existingBiogasFuelKW : Nat
    utilityInputKW : Nat
    totalInputKW : Nat
    methaneProductKW : Nat
    steamProductKW : Nat
    totalInput :
      electrolysisElectricityKW +
        (existingBiogasFuelKW + utilityInputKW)
        ≡ totalInputKW
open PublishedBiogasPilotLedger public

moioliPublishedLedger : PublishedBiogasPilotLedger
moioliPublishedLedger = record
  { electrolysisElectricityKW = 188
  ; existingBiogasFuelKW = 130
  ; utilityInputKW = 34
  ; totalInputKW = 352
  ; methaneProductKW = 248
  ; steamProductKW = 19
  ; totalInput = refl
  }

reportedFeedInputReconciliation :
  electrolysisElectricityKW moioliPublishedLedger
  + (existingBiogasFuelKW moioliPublishedLedger +
     utilityInputKW moioliPublishedLedger)
    ≡ totalInputKW moioliPublishedLedger
reportedFeedInputReconciliation = refl

reportedUsefulHeatAndSNG :
  methaneProductKW moioliPublishedLedger
  + steamProductKW moioliPublishedLedger
    ≡ 267
reportedUsefulHeatAndSNG = refl

-- 352 * .70 ~= 246.4 ; the original authors' reported 70% and 76%
-- are rounded, and are not substituted for the exact fractions:
-- SNG 248/352, combined 267/352.
reportedProductRatioNumerator :
  methaneProductKW moioliPublishedLedger * 1000 ≡ 248000
reportedProductRatioNumerator = refl

reportedProductAndHeatRatioNumerator :
  (methaneProductKW moioliPublishedLedger +
   steamProductKW moioliPublishedLedger) * 1000
     ≡ 267000
reportedProductAndHeatRatioNumerator = refl

-- Different sources cannot be silently dropped when constructing
-- electrical-only production claims. A high product/electric ratio is
-- not an excess-energy demonstration; carbon-rich biogas supplies fuel.
record AttributionAndTransportReceipt : Set₁ where
  field
    pilot : PublishedBiogasPilotLedger
    actualPublicationAndRawMeasurementSource : Set
    sourcePointSpecificDutyAndGasIdentity : Set
    transferToSelectedHydrocarbonStationJustified : Set
    electricityAndBiogasAndUtilityMeterValidation : Set
    stationSolarAndCO2CaptureProvision : Set
    noArtificialSourceOmission : Set
