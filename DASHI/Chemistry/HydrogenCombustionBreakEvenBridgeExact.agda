module DASHI.Chemistry.HydrogenCombustionBreakEvenBridgeExact where

-- Attribution: reusable order cancellation is owned by
-- DASHI.Chemistry.HydrogenFuelCycleBreakEvenExact, which in turn reuses
-- constructive arithmetic from DASHI.Core.Prelude.
-- Matched-output combustion accounting is owned by
-- DASHI.Chemistry.HydrogenFuelCycleExact.
-- This glue layer was user-directed and ChatGPT-drafted (2026-11-09).
-- No engine measurement is claimed by this abstract bridge.

open import DASHI.Core.Prelude using (Nat; _+_; _<_; _≡_; refl)
import DASHI.Chemistry.HydrogenFuelCycleExact as Engine
import DASHI.Chemistry.HydrogenFuelCycleBreakEvenExact as Savings

-- The user must provide a single matched-output run and a fuel-displacement
-- record whose baseline/assisted fuel numbers really refer to that SAME run.
-- This prevents promotion of a fuel-saving table from another apparatus,
-- operating load, or observation into the current engine comparison.
record SameRunFuelSaving : Set where
  field
    engine : Engine.MatchedOutputCombustion
    displacement : Savings.FossilDisplacement
    sameBaseline :
      Savings.baselineFuel displacement ≡ Engine.baselineDiesel engine
    sameAssisted :
      Savings.assistedFuel displacement ≡ Engine.assistedDiesel engine

open SameRunFuelSaving public

-- The exact decision criterion lives on the source-connected displacement
-- record. No extraneous physical or corporate identity is introduced.
sameRunEnergySavingIff :
  (s : SameRunFuelSaving) →
  Savings.Equivalence
    (Savings.assistedFuel (displacement s)
       + Savings.externalElectricity (displacement s)
       < Savings.baselineFuel (displacement s))
    (Savings.externalElectricity (displacement s)
       < Savings.displacedFuel (displacement s))
sameRunEnergySavingIff s =
  Savings.energySavingIffDisplacementExceedsElectricity (displacement s)

-- Concrete arithmetic regression: matched output at 35% on 100 diesel
-- and 50% on 70 diesel, with no H2 energy, already in Engine.
-- This source corresponds to the same 30% displacement example.
sampleSameRun : SameRunFuelSaving
sampleSameRun = record
  { engine = Engine.thirtyPercentWithoutSubstitution
  ; displacement = record
      { baselineFuel = 100
      ; assistedFuel = 70
      ; displacedFuel = 30
      ; externalElectricity = 0
      ; exactDisplacement = refl
      }
  ; sameBaseline = refl
  ; sameAssisted = refl
  }

-- This toy certificate demonstrates logical satisfiability. Neither the
-- assumed engine efficiency change nor any 30% device claim is validated.
