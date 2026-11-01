{-# OPTIONS --safe #-}

module DASHI.Physics.Semiconductor.Deposition.CVDTransportReactionExact where

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)

-- Sources:
-- Luzhao Sun et al., "Chemical vapour deposition",
-- Nature Reviews Methods Primers 1, 5 (2021), stable article identifier:
-- https://www.nature.com/articles/s43586-020-00005-y
--
-- "On the modelling of transport phenomena in chemical vapour deposition and
-- its use in reactor design and process optimization",
-- Thin Solid Films 206 (1991) 47–53,
-- DOI: 10.1016/0040-6090(91)90391-A.
--
-- These sources motivate separating gas delivery, gas-phase chemistry,
-- surface arrival, surface reaction, incorporation, and by-product removal.

record CVDState : Set where
  constructor cvdState
  field
    inletPrecursorCode   : Nat
    nearSurfacePrecursor : Nat
    gasPhaseProducts     : Nat
    adsorbedReactants    : Nat
    incorporatedUnits    : Nat
    desorbedByproducts   : Nat
    temperatureCode      : Nat

open CVDState public

-- Two synthetic reactor states with the same inlet precursor but different
-- near-surface transport and therefore different incorporation.
transportRich : CVDState
transportRich = cvdState 100 80 10 65 50 15 700

transportLimited : CVDState
transportLimited = cvdState 100 40 25 30 20 10 700

sameInlet : inletPrecursorCode transportRich ≡ inletPrecursorCode transportLimited
sameInlet = refl

sameTemperature : temperatureCode transportRich ≡ temperatureCode transportLimited
sameTemperature = refl

data ⊥ : Set where

inletDoesNotDetermineSurfaceSupply :
  nearSurfacePrecursor transportRich ≡ nearSurfacePrecursor transportLimited → ⊥
inletDoesNotDetermineSurfaceSupply ()

inletDoesNotDetermineGrowth :
  incorporatedUnits transportRich ≡ incorporatedUnits transportLimited → ⊥
inletDoesNotDetermineGrowth ()

-- Surface branch bookkeeping: incorporated + byproduct = reacted inventory.
record SurfaceReactionPartition : Set where
  constructor surfaceReactionPartition
  field
    reactedInventory : Nat
    incorporated     : Nat
    byproduct        : Nat
    conservation     : incorporated + byproduct ≡ reactedInventory

open SurfaceReactionPartition public

syntheticSurfacePartition : SurfaceReactionPartition
syntheticSurfacePartition = surfaceReactionPartition 65 50 15 refl

-- Firewall:
-- same inlet flow and substrate temperature != same film growth.  Boundary-layer
-- transport, gas-phase chemistry, sticking, surface kinetics and depletion can
-- independently break descent.
data CVDResidual : Set where
  GasPhaseReactionNetwork   : CVDResidual
  BoundaryLayerTransport    : CVDResidual
  DiffusionCoefficient      : CVDResidual
  SurfaceStickingProbability : CVDResidual
  SurfaceReactionRate       : CVDResidual
  NucleationDensity         : CVDResidual
  FilmStress                : CVDResidual
  ImpurityIncorporation     : CVDResidual
  StepCoverage              : CVDResidual
  ExactProductionRecipe     : CVDResidual
