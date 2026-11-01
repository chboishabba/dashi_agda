module DASHI.Biology.Physical.CompartmentMembraneTransportExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
-- Peter Mitchell,
-- "Coupling of Phosphorylation to Electron and Hydrogen Transfer by a
-- Chemi-Osmotic type of Mechanism", Nature 191 (1961), 144-148.
-- DOI: 10.1038/191144a0.
--
-- DASHI CONTRIBUTION
-- A conservative finite membrane-transport regression and an SI signature for
-- compartment geometry, permeability, voltage, surface tension and osmotic
-- pressure.  The unit-step transport law is deliberately not promoted as a
-- calibrated electrochemical constitutive equation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Units.SI as SI
import DASHI.Biology.Physical.SIBiologyDimensionsExact as BioSI

record CompartmentState : Set where
  constructor compartmentState
  field
    inside outside : Nat

open CompartmentState public

totalSolute : CompartmentState → Nat
totalSolute (compartmentState i o) = i + o

-- Move one available solute quantum from outside to inside.
permeateInward : CompartmentState → CompartmentState
permeateInward (compartmentState i zero) = compartmentState i zero
permeateInward (compartmentState i (suc o)) = compartmentState (suc i) o

permeationConservesSolute :
  (x : CompartmentState) → totalSolute (permeateInward x) ≡ totalSolute x
permeationConservesSolute (compartmentState i zero)
  rewrite +-identityʳ i = refl
permeationConservesSolute (compartmentState i (suc o))
  rewrite +-suc i o = refl

record MembraneCompartmentSISignature : Set₁ where
  field
    membraneArea : Set
    compartmentVolume : Set
    permeability : Set
    transmembraneVoltage : Set
    surfaceTension : Set
    osmoticPressure : Set
    concentration : Set
    electrochemicalPotential : Set

    areaIsSI : membraneArea ≡ SI.Quantity SI.Area SI.unitScale
    volumeIsSI : compartmentVolume ≡ SI.Quantity SI.Volume SI.unitScale
    permeabilityIsVelocityDimension :
      permeability ≡ SI.Quantity SI.Velocity SI.unitScale
    voltageIsSI : transmembraneVoltage ≡ SI.Quantity SI.Voltage SI.milliScale
    surfaceTensionIsSI :
      surfaceTension ≡ SI.Quantity BioSI.SurfaceTension SI.unitScale
    osmoticPressureIsSI : osmoticPressure ≡ SI.Quantity SI.Pressure SI.unitScale
    concentrationIsSI :
      concentration ≡ SI.Quantity SI.MolarConcentration SI.unitScale
    electrochemicalPotentialIsMolarEnergy :
      electrochemicalPotential ≡ SI.Quantity SI.MolarEnergy SI.unitScale

open MembraneCompartmentSISignature public

canonicalMembraneCompartmentSISignature : MembraneCompartmentSISignature
canonicalMembraneCompartmentSISignature = record
  { membraneArea = SI.Quantity SI.Area SI.unitScale
  ; compartmentVolume = SI.Quantity SI.Volume SI.unitScale
  ; permeability = SI.Quantity SI.Velocity SI.unitScale
  ; transmembraneVoltage = SI.Quantity SI.Voltage SI.milliScale
  ; surfaceTension = SI.Quantity BioSI.SurfaceTension SI.unitScale
  ; osmoticPressure = SI.Quantity SI.Pressure SI.unitScale
  ; concentration = SI.Quantity SI.MolarConcentration SI.unitScale
  ; electrochemicalPotential = SI.Quantity SI.MolarEnergy SI.unitScale
  ; areaIsSI = refl
  ; volumeIsSI = refl
  ; permeabilityIsVelocityDimension = refl
  ; voltageIsSI = refl
  ; surfaceTensionIsSI = refl
  ; osmoticPressureIsSI = refl
  ; concentrationIsSI = refl
  ; electrochemicalPotentialIsMolarEnergy = refl
  }
