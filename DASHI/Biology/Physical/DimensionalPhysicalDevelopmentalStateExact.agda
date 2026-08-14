module DASHI.Biology.Physical.DimensionalPhysicalDevelopmentalStateExact where

------------------------------------------------------------------------
-- One dimensionally checked cross-scale physical state.  Regulatory and goal
-- coordinates are typed informational/control carriers; physical coordinates
-- use the existing SI Quantity indices so unlike dimensions cannot be mixed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Units.SI as SI
import DASHI.Biology.Physical.SIBiologyDimensionsExact as BioSI
import DASHI.Biology.Physical.MechanochemicalMorphogenesisSIExact as Mech
import DASHI.Biology.Physical.DevelopmentalGoalFactorizationExact as Goal

record DimensionalPhysicalDevelopmentalState : Set where
  constructor dimensionalPhysicalDevelopmentalState
  field
    concentration : SI.Quantity SI.MolarConcentration SI.unitScale
    morphogenReactionRate : SI.Quantity BioSI.MolarReactionRate SI.unitScale
    membranePotential : SI.Quantity SI.Voltage SI.milliScale
    ionicCurrent : SI.Quantity SI.Current SI.nanoScale
    junctionConductance : SI.Quantity SI.Conductance SI.nanoScale
    metabolicFreeEnergy : SI.Quantity SI.MolarEnergy SI.unitScale
    mechanicalStress : SI.Quantity SI.Pressure SI.unitScale
    tissueVelocity : SI.Quantity SI.Velocity SI.unitScale
    forceDensity : SI.Quantity BioSI.ForceDensity SI.unitScale
    regulatoryState : Bool
    goal : Goal.DevelopmentalGoal

open DimensionalPhysicalDevelopmentalState public

canonicalZeroPhysicalState : DimensionalPhysicalDevelopmentalState
canonicalZeroPhysicalState = dimensionalPhysicalDevelopmentalState
  SI.zeroQ
  SI.zeroQ
  SI.zeroQ
  SI.zeroQ
  SI.zeroQ
  SI.zeroQ
  SI.zeroQ
  SI.zeroQ
  SI.zeroQ
  false
  Goal.leftHandHereOurs

zeroStateVoltageIsDimensionChecked :
  membranePotential canonicalZeroPhysicalState
    ≡ (SI.zeroQ {d = SI.Voltage} {s = SI.milliScale})
zeroStateVoltageIsDimensionChecked = refl

zeroStateStressIsDimensionChecked :
  mechanicalStress canonicalZeroPhysicalState
    ≡ (SI.zeroQ {d = SI.Pressure} {s = SI.unitScale})
zeroStateStressIsDimensionChecked = refl
