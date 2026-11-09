module DASHI.Chemistry.HydrogenElectrolyserEnergyExact where

-- Source owner: standard first-law accounting and natural-number order,
-- reused from DASHI.Core.Prelude and the existing industrial ledger.
-- User-directed, ChatGPT-drafted conditional formalisation (2026-11-09).
-- No efficiency value, hydrogen output or actual apparatus is asserted.
-- A meter-calibrated source record must supply the physical first-law
-- equality on a consistent HHV and SI energy basis.

open import DASHI.Core.Prelude
  using (Nat; _+_; _≤_; _≡_; refl; sym; subst; m≤m+n)

record ElectrolyserFirstLaw : Set where
  field
    electricalWork : Nat
    generatedHydrogenHHV : Nat
    heatAndOtherLosses : Nat
    storedEnergyIncrease : Nat
    balance :
      electricalWork ≡
      generatedHydrogenHHV +
        (heatAndOtherLosses + storedEnergyIncrease)

open ElectrolyserFirstLaw public

-- The bound is derived from the supplied first-law equality and
-- nonnegative residual energy; it is NOT a vendor-specific measurement.
hydrogenHHVWithinElectricity :
  (s : ElectrolyserFirstLaw) →
  generatedHydrogenHHV s ≤ electricalWork s
hydrogenHHVWithinElectricity s =
  subst
    (λ bound → generatedHydrogenHHV s ≤ bound)
    (sym (balance s))
    (m≤m+n
      (generatedHydrogenHHV s)
      (heatAndOtherLosses s + storedEnergyIncrease s))

-- A closed energy budget cannot pay for two separately counted amounts
-- greater than the produced stream; routing must first use a unique
-- allocation certificate from HydrogenFuelCycleExact.
record MeteredProductionReceipt : Set where
  field
    process : ElectrolyserFirstLaw
    electricalMeterReference : Nat
    hydrogenMeterReference : Nat
    commonHHVAndUnitVerified : Set
    independentCalibrationAvailable : Set

open MeteredProductionReceipt public

-- No inhabitant of MeteredProductionReceipt is fabricated from marketing
-- copy, a patent abstract or the existence of these record types.
