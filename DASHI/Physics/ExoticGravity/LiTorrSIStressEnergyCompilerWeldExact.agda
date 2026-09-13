module DASHI.Physics.ExoticGravity.LiTorrSIStressEnergyCompilerWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGSIMetrologyBridgeExact as SIM
import DASHI.Physics.ExoticGravity.LiTorrSignedSIMassCurrentCompilerExact as Jm
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryStressEnergyCompilationExact as StressCompile
import DASHI.Physics.ExoticGravity.SuperconductingChargeMassCurrentBidiExact as Current

------------------------------------------------------------------------
-- LI-TORR SI MASS-CURRENT -> LABORATORY STRESS-ENERGY WELD
--
-- The signed J_m field is one source coordinate, not the full T_{mu nu}.
-- This module requires independent SI energy-density / momentum-density /
-- spatial-stress measurements plus frame, tensor-assembly and same-apparatus
-- receipts before invoking the existing stress-energy compiler.
------------------------------------------------------------------------

record SIStressEnergyMeasurementBundle : Set where
  constructor si-stress-energy-measurement-bundle
  field
    energyDensity : SI.Measurement SIM.EnergyDensity SI.unitScale
    momentumDensity : SI.Measurement SIM.MomentumDensity SI.unitScale
    spatialStress : SI.Measurement SI.Pressure SI.unitScale
    measurementRevision : String

open SIStressEnergyMeasurementBundle public

record SIStressEnergyWeldInput : Set₁ where
  constructor si-stress-energy-weld-input
  field
    apparatusIdentity : String
    signedMassCurrent : Jm.SignedSIMassCurrentField
    existingMassCurrentReceipt : Current.MassCurrentSourceReconstructionReceipt
    measurements : SIStressEnergyMeasurementBundle
    FrameAndConventionReceipt : Set
    frameAndConventionReceipt : FrameAndConventionReceipt
    TensorAssemblyReceipt : Set
    tensorAssemblyReceipt : TensorAssemblyReceipt
    SameApparatusIdentityReceipt : Set
    sameApparatusIdentityReceipt : SameApparatusIdentityReceipt
    signedFieldSameApparatus : Bool
    measurementsSameApparatus : Bool

open SIStressEnergyWeldInput public

compileSIStressEnergyInput :
  SIStressEnergyWeldInput → StressCompile.LaboratoryStressEnergyCompilationInput
compileSIStressEnergyInput input =
  StressCompile.laboratory-stress-energy-compilation-input
    (SIStressEnergyWeldInput.apparatusIdentity input)
    (SIStressEnergyWeldInput.existingMassCurrentReceipt input)
    (SI.Measurement SIM.EnergyDensity SI.unitScale)
    (SIStressEnergyMeasurementBundle.energyDensity
      (SIStressEnergyWeldInput.measurements input))
    (SI.Measurement SIM.MomentumDensity SI.unitScale)
    (SIStressEnergyMeasurementBundle.momentumDensity
      (SIStressEnergyWeldInput.measurements input))
    (SI.Measurement SI.Pressure SI.unitScale)
    (SIStressEnergyMeasurementBundle.spatialStress
      (SIStressEnergyWeldInput.measurements input))
    (SIStressEnergyWeldInput.FrameAndConventionReceipt input)
    (SIStressEnergyWeldInput.frameAndConventionReceipt input)
    (SIStressEnergyWeldInput.TensorAssemblyReceipt input)
    (SIStressEnergyWeldInput.tensorAssemblyReceipt input)
    (SIStressEnergyWeldInput.SameApparatusIdentityReceipt input)
    (SIStressEnergyWeldInput.sameApparatusIdentityReceipt input)

record SIStressEnergyBoundary : Set where
  constructor si-stress-energy-boundary
  field
    signedMassCurrentEqualsFullStressEnergy : Bool
    energyDensityRequiredSeparately : Bool
    momentumDensityRequiredSeparately : Bool
    spatialStressRequiredSeparately : Bool
    frameConventionRequired : Bool
    tensorAssemblyRequired : Bool
    sameApparatusIdentityRequired : Bool
    siTypingAlonePaysAnyMeasurement : Bool
    compiledStressEnergyAutomaticallyProvesAnomaly : Bool

canonicalSIStressEnergyBoundary : SIStressEnergyBoundary
canonicalSIStressEnergyBoundary =
  si-stress-energy-boundary
    false true true true true true true false false
