module DASHI.Chemistry.HydrogenProcessFullBoundaryExact where

-- Attribution: First-law open-system accounting is standard prior physics.
-- DASHI.Physics.Units.SI and IndustrialReactiveEnergyBalanceExact are the
-- preexisting typed owner / generic ledger. This explicit multicarrier
-- ledger was directed by the user and drafted by ChatGPT (2026-11-09).
-- It is NOT a measurement or a statement about McLaren patent ownership.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Data.Nat.Properties using (m≤m+n)
open import Relation.Binary.PropositionalEquality using (sym; subst)
import DASHI.Physics.Units.SI as SI

-- All fields represent energy in one coherent joule/HHV-equivalent
-- accounting convention, not voltage, flow-rate or thermal power.
-- Imported thermal and chemical energy are *not* omitted merely because
-- the local hydrogen generator is described as a low-voltage device.
record FullProcessEnergyBoundary : Set where
  field
    gridOrBatteryElectricity : Nat
    importedHeat : Nat
    additionalChemicalFeed : Nat
    storedEnergyBefore : Nat

    hydrogenChemicalHHV : Nat
    usefulWorkExport : Nat
    rejectedHeat : Nat
    otherEnergyExport : Nat
    storedEnergyAfter : Nat

    firstLaw :
      ((gridOrBatteryElectricity + importedHeat)
          + (additionalChemicalFeed + storedEnergyBefore))
        ≡ hydrogenChemicalHHV +
          (usefulWorkExport + (rejectedHeat
              + (otherEnergyExport + storedEnergyAfter)))

open FullProcessEnergyBoundary public

totalInputEnergy : FullProcessEnergyBoundary → Nat
totalInputEnergy b =
  (gridOrBatteryElectricity b + importedHeat b)
  + (additionalChemicalFeed b + storedEnergyBefore b)

nonHydrogenOutputEnergy : FullProcessEnergyBoundary → Nat
nonHydrogenOutputEnergy b =
  usefulWorkExport b + (rejectedHeat b
    + (otherEnergyExport b + storedEnergyAfter b))

hydrogenBoundedByAllInputs :
  (b : FullProcessEnergyBoundary) →
  hydrogenChemicalHHV b ≤ totalInputEnergy b
hydrogenBoundedByAllInputs b =
  subst
    (λ n → hydrogenChemicalHHV b ≤ n)
    (sym (firstLaw b))
    (m≤m+n (hydrogenChemicalHHV b) (nonHydrogenOutputEnergy b))

-- Typed meter carriers must be paid separately. The Nat equality is not
-- a source-derived empirical measurement or evidence for >100% operation.
record PhysicalEnergyReceipt : Set₁ where
  field
    boundary : FullProcessEnergyBoundary
    electricalMeter : SI.Measurement SI.Energy SI.unitScale
    importedHeatMeter : SI.Measurement SI.Energy SI.unitScale
    chemicalFeedCalorimetry : Set
    storageDifferenceMetered : Set
    hydrogenMeterAndHHVReference : Set
    timeAlignedBoundary : Set
    independentCalibrationAndUncertainty : Set
