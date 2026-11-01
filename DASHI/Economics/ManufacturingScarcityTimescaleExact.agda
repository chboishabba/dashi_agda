module DASHI.Economics.ManufacturingScarcityTimescaleExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- MANUFACTURING SCARCITY / TIMESCALE MISMATCH
------------------------------------------------------------------------

data ManufacturingStage : Set where
  foundry : ManufacturingStage
  hbm : ManufacturingStage
  advancedPackaging : ManufacturingStage
  networking : ManufacturingStage
  power : ManufacturingStage

record ManufacturingScarcitySystem : Set₁ where
  field
    Time Asset : Set
    Capacity Demand MarketPrice LongRunCompetitiveCost :
      ManufacturingStage → Time → Set
    EconomicResidualValue PhysicalFunctionality : Asset → Time → Set
    SoftwareTimescale HardwareTimescale InfrastructureTimescale : Set

open ManufacturingScarcitySystem public

record Scarcity
    (sys : ManufacturingScarcitySystem)
    (stage : ManufacturingStage)
    (time : Time sys) : Set₁ where
  field
    capacityObserved : Capacity sys stage time
    demandObserved   : Demand sys stage time
    demandExceedsCapacity : Set

record ScarcityRent
    (sys : ManufacturingScarcitySystem)
    (stage : ManufacturingStage)
    (time : Time sys) : Set₁ where
  field
    marketPriceObserved : MarketPrice sys stage time
    longRunCostObserved : LongRunCompetitiveCost sys stage time
    positiveScarcityRent : Set

record TimescaleMismatch (sys : ManufacturingScarcitySystem) : Set₁ where
  field
    softwareFasterThanHardware : Set
    hardwareFasterThanInfrastructure : Set

record PotentialStrandedCapital
    (sys : ManufacturingScarcitySystem)
    (asset : Asset sys) : Set₁ where
  field
    fastTechnologyChange : Set
    slowCapitalDeployment : Set
    futureEconomicMismatch : Set

record FunctioningButEconomicallyImpaired
    (sys : ManufacturingScarcitySystem)
    (asset : Asset sys)
    (time : Time sys) : Set₁ where
  field
    physicallyFunctions : PhysicalFunctionality sys asset time
    economicallyImpaired : Set

data ScarcityRentImpliesDownstreamViabilityPermission : Set where

data PhysicalFunctionalityImpliesHighResidualValuePermission : Set where

data TimescaleMismatchImpliesActualStrandingPermission : Set where

scarcityRentDoesNotAutoPromoteToDownstreamViability :
  ScarcityRentImpliesDownstreamViabilityPermission → ⊥
scarcityRentDoesNotAutoPromoteToDownstreamViability ()

physicalFunctionalityDoesNotAutoPromoteToHighResidualValue :
  PhysicalFunctionalityImpliesHighResidualValuePermission → ⊥
physicalFunctionalityDoesNotAutoPromoteToHighResidualValue ()

timescaleMismatchDoesNotAutoPromoteToActualStranding :
  TimescaleMismatchImpliesActualStrandingPermission → ⊥
timescaleMismatchDoesNotAutoPromoteToActualStranding ()
