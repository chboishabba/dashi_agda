module DASHI.Environment.DataCentreThermalReuseMetricBoundaryExact where

-- ISO/IEC 30134-6:2021 illustrative metric scope, 2026-10-24.
-- All equalities are on finite natural-number examples; actual ISO ERF requires
-- auditable reuse meter boundaries and evidence of beneficial external use.
-- This module proves neither a general ERF standard conformance nor an observed
-- facility value. Unit: 100 kW as in DataCentreThermalReuseBalanceExact.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Environment.DataCentreThermalReuseBalanceExact as Thermal

data AccountingBoundary : Set where
  facilityElectricalBoundary : AccountingBoundary
  heatTransferredAtFacilityBoundary : AccountingBoundary
  compressorElectricityExternal : AccountingBoundary
  usefulHeatAtCustomerBoundary : AccountingBoundary
  customerThermalNetworkLoss : AccountingBoundary

data MeterQuality : Set where
  merelyProposed : MeterQuality
  syntheticChecked : MeterQuality
  calibratedAndReconciled : MeterQuality
  independentlyAudited : MeterQuality

-- The illustrative fixture is a stationary 10-MW IT / 12.5-MW facility.
-- Source-origin heat = 2MW directly reused + 6MW HP evaporator stream.
-- Additional 2.4MW compressor power is NOT data-centre waste heat.
fixtureSourceReused : Nat
fixtureSourceReused =
  Thermal.directReuseHundredKilowatt + Thermal.hpEvaporatorHundredKilowatt

fixtureDelivered : Nat
fixtureDelivered = Thermal.totalExportHundredKilowatt

fixtureDataCentreElectric : Nat
fixtureDataCentreElectric = Thermal.sitePowerHundredKilowatt

fixtureIT : Nat
fixtureIT = Thermal.itHundredKilowatt

-- A hypothetical ERF 80/125 equals 64%, NOT 104/125.
erfSixtyFourPercent :
  100 * fixtureSourceReused ≡ 64 * fixtureDataCentreElectric
erfSixtyFourPercent = refl

pueOnePointTwoFive :
  100 * fixtureDataCentreElectric ≡ 125 * fixtureIT
pueOnePointTwoFive = refl

-- ERE = (1 - ERF)*PUE for this simplified identical-period case:
-- (125 - 80)/100 = 0.45. Avoid subtraction by exact additive witness.
remainingFortyFiveUnits :
  fixtureSourceReused + 45 ≡ fixtureDataCentreElectric
remainingFortyFiveUnits = refl

ereFortyFivePercent :
  100 * 45 ≡ 45 * fixtureIT
ereFortyFivePercent = refl

-- Customer heat = site recovered heat plus external compressor input.
hotOutputDecomposition :
  fixtureDelivered ≡ fixtureSourceReused + Thermal.hpElectricHundredKilowatt
hotOutputDecomposition = refl

hotOutputIsNotSourceOnly :
  fixtureDelivered ≡ fixtureSourceReused → ⊥
hotOutputIsNotSourceOnly ()

-- Incorrect promotion from heat output (104 units) to the 64% ERF numerator.
wrongEightyThreePointTwoPercentAsSixtyFour :
  100 * fixtureDelivered ≡ 64 * fixtureDataCentreElectric → ⊥
wrongEightyThreePointTwoPercentAsSixtyFour ()

-- Offtake absent: potential can be 80 but recovered energy can be zero.
-- This is a finite counterexample to equating potential and realised ERF.
samePotential :
  Thermal.heatAvailableHundredKilowatt Thermal.matchedOfftaker
  ≡ Thermal.heatAvailableHundredKilowatt Thermal.noConcurrentOfftaker
samePotential = refl

missingOfftakeMeansZeroRealised :
  Thermal.heatActuallyRecoveredHundredKilowatt Thermal.noConcurrentOfftaker
  ≡ 0
missingOfftakeMeansZeroRealised = refl

-- The numerical identity is NOT a measurement source. Units, network heat
-- losses, external HP boundary, offsite beneficial use and facility/nonfacility
-- transfers must be audited before any actual ERF/ERE/PUE claim.
