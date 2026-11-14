module DASHI.Chemistry.HydrogenOxygenFactorialIdentificationExact where

-- Attribution (2026-11-09): a 2x2 factorial contrast is standard
-- experimental-design mathematics, not an invention of McLaren/DASHI.
-- The user requested identifying H2, O2, combined and power-only effects;
-- ChatGPT drafted this conditional source. Prior DASHI test-arm names are
-- in DASHI.Chemistry.HydrogenFuelCycleDeviceEvidenceExact.
-- No real device is shown to have a nonzero interaction by this module.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_)
import DASHI.Physics.Units.SI as SI

-- Diesel inputs are comparable only at exactly the same useful output,
-- engine operating point, and test-block boundary. Such assumptions belong to the separate CausalAdmission record and are
-- not assumed by the pure four-number contrast.
record FactorialDieselBlock : Set where
  field
    noHydrogenNoOxygen : Nat
    hydrogenOnly : Nat
    oxygenOnly : Nat
    hydrogenAndOxygen : Nat
open FactorialDieselBlock public

-- More combined diesel displacement than the sum of separate effects
-- requires the following cross contrast. It is an *operational contrast*;
-- attributing it to chemistry additionally needs causal design receipts.
record PositiveInteraction (b : FactorialDieselBlock) : Set where
  field
    extraCombinedDieselSaving : Nat
    witnessedContrast :
      (noHydrogenNoOxygen b + hydrogenAndOxygen b)
        + extraCombinedDieselSaving
        ≡ hydrogenOnly b + oxygenOnly b

open PositiveInteraction public

-- In the example a power-only baseline burns 100, H-only 92, O-only 94,
-- combined 80: the additive prediction is 86 and the interaction is 6.
-- All are synthetic fixtures and cannot be labelled field measurements.
toyFactorialBlock : FactorialDieselBlock
toyFactorialBlock = record
  { noHydrogenNoOxygen = 100
  ; hydrogenOnly = 92
  ; oxygenOnly = 94
  ; hydrogenAndOxygen = 80

  }

toyInteraction : PositiveInteraction toyFactorialBlock
toyInteraction = record
  { extraCombinedDieselSaving = 6
  ; witnessedContrast = refl
  }

-- Critically, the source study cannot produce this witness merely from
-- named treatment arms: positive interaction + a metered fuel-input
-- comparison STILL does not prove the electrical energy cost is recovered.
record CausalAdmission (b : FactorialDieselBlock) : Set₁ where
  field
    factorial : PositiveInteraction b
    pairedOutputSame : Set
    pairedLoadSpeedAmbientSame : Set
    hydrogenDoseSameInRelevantArms : Set
    oxygenDoseSameInRelevantArms : Set
    powerOnlyPlaceboControlled : Set
    crossoverAndOrderControlled : Set
    fuelMeterTraceable : Set
    externalInputAndInventoryRecorded : Set
    reproducibleExperiment : Set
    noxAndParticleEmissionUncertainty : Set
    completeEnergyInputAndOutputReceipt : Set
    independentlyReplicated : Set
