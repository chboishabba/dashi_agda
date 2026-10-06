module DASHI.Physics.Plasma.CommercialFusionPlantObjectiveExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Plasma.MagneticConfinementMachineExact as Confinement

------------------------------------------------------------------------
-- COMMERCIAL FUSION POWER-PLANT OBJECTIVE
--
-- Plasma gain is not the consumer objective.  The consumer is a plant that
-- exports electricity while closing fuel, heat, maintenance, materials and
-- availability obligations.  All quantities below are state-indexed so that
-- a plasma result cannot silently become a plant result.
--
-- Fuel-cycle obligations remain generic here.  D-T instantiations may require
-- tritium breeding/inventory closure; p-11B instantiations instead inherit
-- advanced-temperature, radiation, ash-removal and charged-product conversion
-- obligations.  Neither fuel is silently universalized by this owner.
------------------------------------------------------------------------

data FusionFuelClass : Set where
  deuteriumTritium : FusionFuelClass
  protonBoron11 : FusionFuelClass
  otherDeclaredFusionFuel : FusionFuelClass

record CommercialFusionPlantState
    (plasma : Confinement.MagneticConfinementState) : Set₁ where
  constructor commercial-fusion-plant-state
  field
    fuelClass : FusionFuelClass
    equilibrium : Confinement.EquilibriumReceipt plasma
    stability : Confinement.StabilityReceipt plasma
    transport : Confinement.TransportReceipt plasma
    fusionPerformance : Confinement.FusionPerformanceReceipt plasma

    fusionThermalPower : SI.Measurement SI.Power SI.unitScale
    grossElectricPower : SI.Measurement SI.Power SI.unitScale
    plasmaHeatingPower : SI.Measurement SI.Power SI.unitScale
    currentDrivePower : SI.Measurement SI.Power SI.unitScale
    cryogenicPower : SI.Measurement SI.Power SI.unitScale
    pumpingPower : SI.Measurement SI.Power SI.unitScale
    fuelCyclePower : SI.Measurement SI.Power SI.unitScale
    balanceOfPlantPower : SI.Measurement SI.Power SI.unitScale
    netElectricPower : SI.Measurement SI.Power SI.unitScale

    heatConversionReceipt : Set
    neutronOrProductEnergyCaptureReceipt : Set
    fuelCycleClosureReceipt : Set
    fuelInventorySelfSufficiencyReceipt : Set
    radiationLossAndRecoveryReceipt : Set
    fusionProductAshRemovalReceipt : Set
    plasmaFacingMaterialLifetimeReceipt : Set
    divertorOrExhaustLifetimeReceipt : Set
    remoteMaintenanceReceipt : Set
    componentReplacementReceipt : Set
    plantAvailabilityReceipt : Set
    gridDeliveryReceipt : Set
    levelizedCostOrCommercialAttractivenessReceipt : Set

    plantAuthority : Authority.ArtifactAuthorityBoundary
    plantReference : String

open CommercialFusionPlantState public

record NetElectricCommercialityReceipt
    {plasma : Confinement.MagneticConfinementState}
    (plant : CommercialFusionPlantState plasma) : Set₁ where
  constructor net-electric-commerciality-receipt
  field
    grossMinusRecirculatingAccountingReceipt : Set
    positiveNetElectricReceipt : Set
    sustainedDutyCycleReceipt : Set
    maintainableAvailabilityReceipt : Set
    closedFuelCycleReceipt : Set
    commerciallyRelevantCostReceipt : Set
    samePlantBoundaryReceipt : Set
    commercialReference : String

open NetElectricCommercialityReceipt public

record CommercialFusionBoundary : Set where
  constructor commercial-fusion-boundary
  field
    plasmaQGreaterThanOneImpliesPositiveNetElectric : Bool
    plasmaQGreaterThanOneImpliesPositiveNetElectricIsFalse :
      plasmaQGreaterThanOneImpliesPositiveNetElectric ≡ false

    longPulsePlasmaImpliesCommercialPlant : Bool
    longPulsePlasmaImpliesCommercialPlantIsFalse :
      longPulsePlasmaImpliesCommercialPlant ≡ false

    highMagneticFieldAloneImpliesCommercialPlant : Bool
    highMagneticFieldAloneImpliesCommercialPlantIsFalse :
      highMagneticFieldAloneImpliesCommercialPlant ≡ false

    compactGeometryAloneImpliesLowerElectricityCost : Bool
    compactGeometryAloneImpliesLowerElectricityCostIsFalse :
      compactGeometryAloneImpliesLowerElectricityCost ≡ false

    fuelClassAloneProvesCommerciality : Bool
    fuelClassAloneProvesCommercialityIsFalse :
      fuelClassAloneProvesCommerciality ≡ false

    netElectricRequiresRecirculatingPowerAccounting : Bool
    netElectricRequiresRecirculatingPowerAccountingIsTrue :
      netElectricRequiresRecirculatingPowerAccounting ≡ true

    commercialPlantRequiresAvailabilityAndMaintenance : Bool
    commercialPlantRequiresAvailabilityAndMaintenanceIsTrue :
      commercialPlantRequiresAvailabilityAndMaintenance ≡ true

canonicalCommercialFusionBoundary : CommercialFusionBoundary
canonicalCommercialFusionBoundary =
  commercial-fusion-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
