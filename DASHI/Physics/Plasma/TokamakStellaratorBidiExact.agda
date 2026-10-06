module DASHI.Physics.Plasma.TokamakStellaratorBidiExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.Plasma.MagneticConfinementMachineExact as Confinement
import DASHI.Physics.Plasma.TokamakConfinementExact as Tokamak
import DASHI.Physics.Plasma.StellaratorConfinementExact as Stellarator

------------------------------------------------------------------------
-- TOKAMAK <-> STELLARATOR SAME-KERNEL BRIDGE
------------------------------------------------------------------------

tokamakConfinementState :
  Tokamak.TokamakState → Confinement.MagneticConfinementState
tokamakConfinementState = Tokamak.confined

stellaratorConfinementState :
  Stellarator.StellaratorState → Confinement.MagneticConfinementState
stellaratorConfinementState = Stellarator.confined

sharedMagneticFieldDimension :
  SI.MagneticFluxDensity ≡ SI.MagneticFluxDensity
sharedMagneticFieldDimension = refl

sharedCurrentDimension :
  SI.Current ≡ SI.Current
sharedCurrentDimension = refl

sharedPressureDimension :
  SI.Pressure ≡ SI.Pressure
sharedPressureDimension = refl

record TokamakStellaratorBoundary : Set where
  constructor tokamak-stellarator-boundary
  field
    sameCanonicalSIKernel : Bool
    sameCanonicalSIKernelIsTrue : sameCanonicalSIKernel ≡ true

    sameU1MaxwellLorentzMHDLawStack : Bool
    sameU1MaxwellLorentzMHDLawStackIsTrue :
      sameU1MaxwellLorentzMHDLawStack ≡ true

    sameConfinementGeometry : Bool
    sameConfinementGeometryIsFalse : sameConfinementGeometry ≡ false

    tokamakPlasmaCurrentRequirementTransfersToStellarator : Bool
    tokamakPlasmaCurrentRequirementTransfersToStellaratorIsFalse :
      tokamakPlasmaCurrentRequirementTransfersToStellarator ≡ false

    stellaratorThreeDimensionalityTransfersToTokamak : Bool
    stellaratorThreeDimensionalityTransfersToTokamakIsFalse :
      stellaratorThreeDimensionalityTransfersToTokamak ≡ false

    eitherDeviceTopologyAloneRanksFusionPerformance : Bool
    eitherDeviceTopologyAloneRanksFusionPerformanceIsFalse :
      eitherDeviceTopologyAloneRanksFusionPerformance ≡ false

canonicalTokamakStellaratorBoundary : TokamakStellaratorBoundary
canonicalTokamakStellaratorBoundary =
  tokamak-stellarator-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
