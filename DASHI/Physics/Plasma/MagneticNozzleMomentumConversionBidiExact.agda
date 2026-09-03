module DASHI.Physics.Plasma.MagneticNozzleMomentumConversionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MAGNETIC-NOZZLE ENERGY/MOMENTUM CONVERSION
--
-- Keep energy release, plasma acceleration, directed momentum flux and vehicle
-- thrust as separate typed coordinates.  A magnetic nozzle is the coupling
-- geometry that can redirect/accelerate magnetized plasma; it is not a theorem
-- that arbitrary plasma energy becomes thrust.
------------------------------------------------------------------------

record NozzlePlasmaState : Set₁ where
  constructor nozzle-plasma-state
  field
    PlasmaEnergy MagneticField MagneticPressure PlasmaCurrent : Set
    RadialMomentum AxialMomentum : Set
    stateReference : String

open NozzlePlasmaState public

record MagneticNozzleGeometry : Set₁ where
  constructor magnetic-nozzle-geometry
  field
    DivergingField : Set
    AxialFieldGradient : Set
    LorentzCoupling : Set
    geometryReference : String

open MagneticNozzleGeometry public

record DirectedMomentumConversion
    (state : NozzlePlasmaState)
    (geometry : MagneticNozzleGeometry) : Set₁ where
  constructor directed-momentum-conversion
  field
    magneticPressureGradientActs : Set
    jCrossBTransfersMomentum : Set
    rearwardAxialMomentumFlux : Set
    conversionReference : String

open DirectedMomentumConversion public

record ThrustReceipt
    (state : NozzlePlasmaState)
    (geometry : MagneticNozzleGeometry) : Set₁ where
  constructor thrust-receipt
  field
    conversion : DirectedMomentumConversion state geometry
    MomentumFlux : Set
    VehicleImpulse : Set
    thrustReference : String

open ThrustReceipt public

record NozzleBidiBoundary : Set where
  constructor nozzle-bidi-boundary
  field
    plasmaEnergyAloneImpliesThrust : Bool
    plasmaEnergyAloneImpliesThrustIsFalse : plasmaEnergyAloneImpliesThrust ≡ false

    magneticFieldAloneImpliesThrust : Bool
    magneticFieldAloneImpliesThrustIsFalse : magneticFieldAloneImpliesThrust ≡ false

    thrustRequiresDirectedMomentumFlux : Bool
    thrustRequiresDirectedMomentumFluxIsTrue :
      thrustRequiresDirectedMomentumFlux ≡ true

    observedThrustUniquelyIdentifiesFusionSource : Bool
    observedThrustUniquelyIdentifiesFusionSourceIsFalse :
      observedThrustUniquelyIdentifiesFusionSource ≡ false

canonicalNozzleBidiBoundary : NozzleBidiBoundary
canonicalNozzleBidiBoundary =
  nozzle-bidi-boundary false refl false refl true refl false refl
