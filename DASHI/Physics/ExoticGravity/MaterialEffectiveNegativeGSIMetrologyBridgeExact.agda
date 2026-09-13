module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGSIMetrologyBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGMassCurrentAcquisitionBidiExact as Acquire

------------------------------------------------------------------------
-- MATERIAL-EFFECTIVE NEGATIVE-G x CANONICAL SI METROLOGY
--
-- Reuse the repository's single SI owner rather than letting the antigravity
-- lane carry free-text or dimensionless placeholders.  This bridge assigns
-- dimensions to the first empirical BIDI leaf; it does not supply measured
-- values and does not promote any exotic-gravity interpretation.
------------------------------------------------------------------------

MassCurrentDensity MomentumDensity EnergyDensity : SI.Dimension
MassCurrentDensity =
  SI.dim SI.minusTwo SI.one SI.minusOne SI.zeroI SI.zeroI SI.zeroI SI.zeroI
MomentumDensity = MassCurrentDensity
EnergyDensity = SI.Pressure

record SIComponentSourceMeasurement : Set where
  constructor si-component-source-measurement
  field
    componentName : String
    density : SI.Measurement SI.Density SI.unitScale
    mass : SI.Measurement SI.Mass SI.unitScale
    charge : SI.Measurement SI.Charge SI.unitScale
    velocity : SI.Measurement SI.Velocity SI.unitScale
    sourceRevision : String

open SIComponentSourceMeasurement public

record SIMassCurrentMeasurement : Set where
  constructor si-mass-current-measurement
  field
    massCurrentDensity : SI.Measurement MassCurrentDensity SI.unitScale
    derivationRevision : String
    sameSourceRevision : Bool

open SIMassCurrentMeasurement public

record SILaboratoryStressEnergySlice : Set where
  constructor si-laboratory-stress-energy-slice
  field
    energyDensity : SI.Measurement EnergyDensity SI.unitScale
    momentumDensity : SI.Measurement MomentumDensity SI.unitScale
    spatialStress : SI.Measurement SI.Pressure SI.unitScale
    compilationRevision : String
    sameApparatus : Bool

open SILaboratoryStressEnergySlice public

------------------------------------------------------------------------
-- Exact linkage to the existing BIDI leaf.
------------------------------------------------------------------------

siBridgePaysNoAcquisitionLeafByConstruction :
  Acquire.MassCurrentAcquisitionLeaf → Bool
siBridgePaysNoAcquisitionLeafByConstruction _ = false

record MaterialEffectiveNegativeGSIBoundary : Set where
  constructor material-effective-negative-g-si-boundary
  field
    canonicalSIUnitsOwnerReused : Bool
    densityHasMassPerVolumeDimension : Bool
    velocityHasLengthPerTimeDimension : Bool
    massCurrentHasMassPerAreaPerTimeDimension : Bool
    energyDensitySharesPressureDimension : Bool
    siTypingAloneSuppliesMeasurement : Bool
    dimensionallyValidMassCurrentProvesNegativeEffectiveG : Bool
    sameObjectRevisionStillRequired : Bool

canonicalMaterialEffectiveNegativeGSIBoundary :
  MaterialEffectiveNegativeGSIBoundary
canonicalMaterialEffectiveNegativeGSIBoundary =
  material-effective-negative-g-si-boundary
    true true true true true false false true
