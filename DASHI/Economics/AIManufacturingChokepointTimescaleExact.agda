module DASHI.Economics.AIManufacturingChokepointTimescaleExact where

open import DASHI.Core.Prelude
import DASHI.Economics.ManufacturingScarcityTimescaleExact as Scarcity
import DASHI.Architecture.SemiconductorBuiltEnvironmentCrossPollinationExact as Fab

------------------------------------------------------------------------
-- AI MANUFACTURING CHOKEPOINT / FAB CROSS-POLLINATION
--
-- Reuses the repo's existing town/building/fab/wafer/chip realisation carrier.
-- This module does not claim a named foundry, memory supplier, packaging line,
-- country, or project has a particular empirical scarcity level.
------------------------------------------------------------------------

record AIFabEconomicSystem : Set₁ where
  field
    scarcitySystem : Scarcity.ManufacturingScarcitySystem
    fabRealisation : Fab.DesignExecutionSystem

open AIFabEconomicSystem public

record UpstreamScarcityDownstreamCompression : Set₁ where
  field
    Upstream Downstream : Set
    upstreamScarcityRent : Upstream
    downstreamMarginCompression : Downstream

open UpstreamScarcityDownstreamCompression public

-- Existing architectural correctness distinctions remain active: a fab/chip
-- execution pipeline being representationally or operationally correct does
-- not manufacture economic success.
fabRepresentationCorrectnessDoesNotCloseOutcomeSuccess :
  Fab.RepresentationCorrectnessImpliesOutcomeSuccessPermission → ⊥
fabRepresentationCorrectnessDoesNotCloseOutcomeSuccess =
  Fab.representationCorrectnessDoesNotAutoPromoteToOutcomeSuccess

scarcityRentDoesNotCloseDownstreamViability :
  Scarcity.ScarcityRentImpliesDownstreamViabilityPermission → ⊥
scarcityRentDoesNotCloseDownstreamViability =
  Scarcity.scarcityRentDoesNotAutoPromoteToDownstreamViability

physicalFunctionDoesNotCloseEconomicResidualValue :
  Scarcity.PhysicalFunctionalityImpliesHighResidualValuePermission → ⊥
physicalFunctionDoesNotCloseEconomicResidualValue =
  Scarcity.physicalFunctionalityDoesNotAutoPromoteToHighResidualValue
