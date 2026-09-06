{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Deposition.ALDSelfLimitingCycleExact where

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Source:
-- Steven M. George,
-- "Atomic Layer Deposition: An Overview",
-- Chemical Reviews 110 (2010) 111–131,
-- DOI: 10.1021/cr900056b.
--
-- George's review describes ALD as alternating, self-limiting surface reactions.
-- This owner models a finite A/purge/B/purge cycle and saturation bookkeeping.
-- It does not assert a production precursor pair, growth-per-cycle value, or
-- TSMC-specific ALD recipe.

data HalfReaction : Set where
  PrecursorA : HalfReaction
  PrecursorB : HalfReaction

record SurfaceSites : Set where
  constructor surfaceSites
  field
    available : Nat
    occupied  : Nat
    total     : Nat
    conservation : available + occupied ≡ total

open SurfaceSites public

bareSurface : SurfaceSites
bareSurface = surfaceSites 100 0 100 refl

saturatedA : SurfaceSites
saturatedA = surfaceSites 0 100 100 refl

-- Once the finite site carrier is saturated, extra A exposure does not create
-- extra occupied sites in this ideal self-limiting abstraction.
record SaturationWitness : Set where
  constructor saturationWitness
  field
    beforeExposure : SurfaceSites
    afterExposure  : SurfaceSites
    stillSaturated : occupied beforeExposure ≡ occupied afterExposure

open SaturationWitness public

syntheticASaturation : SaturationWitness
syntheticASaturation = saturationWitness saturatedA saturatedA refl

record ALDCycle : Set where
  constructor aldCycle
  field
    startSites       : Nat
    afterAOccupied   : Nat
    afterPurgeA      : Nat
    afterBOccupied   : Nat
    afterPurgeB      : Nat
    incorporatedUnits : Nat

open ALDCycle public

syntheticCycle : ALDCycle
syntheticCycle = aldCycle 100 100 100 100 100 100

-- Exact ideal accumulation seam: cycles * unitsPerCycle = totalUnits.
record IdealCycleAccumulation : Set where
  constructor idealCycleAccumulation
  field
    cycles        : Nat
    unitsPerCycle : Nat
    totalUnits    : Nat
    accumulation  : cycles * unitsPerCycle ≡ totalUnits

open IdealCycleAccumulation public

syntheticTenCycles : IdealCycleAccumulation
syntheticTenCycles = idealCycleAccumulation 10 3 30 refl

-- Firewall:
-- self-limiting chemistry != constant physical thickness per cycle under all
-- conditions.  Nucleation delay, steric effects, temperature, precursor dose,
-- purge completeness, plasma assistance, and feature transport remain separate.
data ALDResidual : Set where
  PrecursorIdentity          : ALDResidual
  SurfaceFunctionalGroup     : ALDResidual
  StericBlocking             : ALDResidual
  NucleationDelay            : ALDResidual
  GrowthPerCycle             : ALDResidual
  TemperatureWindow          : ALDResidual
  PrecursorDose              : ALDResidual
  PurgeCompleteness          : ALDResidual
  PlasmaAssistance           : ALDResidual
  HighAspectRatioConformality : ALDResidual
  ExactProductionRecipe      : ALDResidual
