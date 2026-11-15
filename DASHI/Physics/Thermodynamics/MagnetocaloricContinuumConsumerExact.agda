module DASHI.Physics.Thermodynamics.MagnetocaloricContinuumConsumerExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Laws.ContinuumMaterialLaws as Continuum
import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial as MCE
import DASHI.Physics.Thermodynamics.CaloricRegenerator as Regen

------------------------------------------------------------------------
-- Continuum consumer for AMR regenerator transport.
--
-- This is the sound point of contact with the repo's Navier-Stokes/continuum
-- content: application-specific mass/momentum/energy balance, fluid closure,
-- and Fourier transport.  The Clay global regularity problem is not a device
-- dependency and no Clay theorem is imported or inferred here.
------------------------------------------------------------------------

record RegeneratorContinuumBridge
  {M : MCE.MagnetocaloricMaterial}
  {G : Regen.RegeneratorGeometry}
  {F : Regen.TransferMedium}
  (R : Regen.CaloricRegenerator M G F) : Set₁ where
  open Regen.CaloricRegenerator R
  field
    balanceSystem : Continuum.ContinuumBalanceSystem
    fluidLaw : Continuum.FluidDynamicsLaw
    diffusionLaw : Continuum.DiffusionTransportLaw

    RegeneratorToBalanceState : Set
    RegeneratorToFluidState : Set
    RegeneratorToDiffusionState : Set

    regeneratorToBalanceState : RegeneratorState → RegeneratorToBalanceState
    regeneratorToFluidState : RegeneratorState → RegeneratorToFluidState
    regeneratorToDiffusionState : RegeneratorState → RegeneratorToDiffusionState

    MassBalanceCompatible : RegeneratorState → Set
    MomentumBalanceCompatible : RegeneratorState → Set
    EnergyBalanceCompatible : RegeneratorState → Set
    FourierTransportCompatible : RegeneratorState → Set
    HydraulicClosureCalibrated : RegeneratorState → Set

    massBalanceCompatible :
      (s : RegeneratorState) → MassBalanceCompatible s
    momentumBalanceCompatible :
      (s : RegeneratorState) → MomentumBalanceCompatible s
    energyBalanceCompatible :
      (s : RegeneratorState) → EnergyBalanceCompatible s
    fourierTransportCompatible :
      (s : RegeneratorState) → FourierTransportCompatible s
    hydraulicClosureCalibrated :
      (s : RegeneratorState) → HydraulicClosureCalibrated s

record RegeneratorContinuumAuthorityBoundary : Set where
  constructor regenerator-continuum-authority-boundary
  field
    continuumBalanceIsRelevant : Bool
    constitutiveClosureRequiresCalibration : Bool
    porousReductionRequiresGeometryEvidence : Bool
    deviceTransportDoesNotRequireClayRegularity : Bool
    clayRegularityDoesNotSupplyDeviceCalibration : Bool
    genericNSMachineryMayBeReusedOnlyAfterPhysicalReduction : Bool

canonicalRegeneratorContinuumAuthorityBoundary : RegeneratorContinuumAuthorityBoundary
canonicalRegeneratorContinuumAuthorityBoundary =
  regenerator-continuum-authority-boundary true true true true true true
