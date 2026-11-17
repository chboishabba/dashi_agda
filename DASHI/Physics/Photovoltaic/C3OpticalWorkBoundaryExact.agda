module DASHI.Physics.Photovoltaic.C3OpticalWorkBoundaryExact where

-- Exploratory proof cut, 2026-11-16. Conditional/synthetic model.
-- NOT a calibrated material Hamiltonian, radiative gain, or RF photovoltaic device.
-- Agda kernel check remains open; local runtime has no Agda installation.

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Algebra.TriadicDepthOneCharacters as Char
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Foundations.TriadicFiniteQuotient as Quotient
import DASHI.Physics.Chemistry.AtomicPeriodicTable369C3FourierSpatialRestrictionExact as Fourier
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as C3
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

------------------------------------------------------------------------
-- Reuse the exact source C3 Fourier square, do NOT reinvent characters.
-- This is NOT yet a dipole selection rule on an actual material.
------------------------------------------------------------------------

c3PhaseTransportSquare :
  (m : C3.MagneticState) ->
  (x shift : Quotient.Residue3Pow Quotient.one) ->
  Fourier.fourierCharacter m (Arithmetic.addResidue x shift)
  ≡ Char.multiplyPhase
      (Fourier.fourierCharacter m x)
      (Char.characterValue (Fourier.frequencyOfMagneticState m) shift)
c3PhaseTransportSquare m x shift =
  Char.characterAdditive (Fourier.frequencyOfMagneticState m) x shift

------------------------------------------------------------------------
-- Same-material admission; an abstract type is not physical calibration.
------------------------------------------------------------------------

record SameMaterialOpticalAdmission : Set₁ where
  field
    Material : Set
    CrystalState : Set
    OpticalState : Set
    selectedCrystalMaterial : Material
    selectedOpticalMaterial : Material
    materialMatches : selectedCrystalMaterial ≡ selectedOpticalMaterial
    crystalHamiltonian : CrystalState -> CrystalState
    opticalObservable : OpticalState -> OpticalState
    selectedOrbitalToOptical : CrystalState -> OpticalState

------------------------------------------------------------------------
-- Signed-port budget: track RF input and recovered drive separately.
-- Thermal extraction is TODO, so thermalBudget remains an output energy.
------------------------------------------------------------------------

record PVDrivenWorkWindow : Set where
  constructor pvDrivenWorkWindow
  field
    solarIncident : Nat
    driverSupplied : Nat
    initialStored : Nat
    grossElectricalExport : Nat
    driverRecovered : Nat
    thermalBudget : Nat
    opticalEscaped : Nat
    finalStored : Nat
    energyBalance :
      (solarIncident + driverSupplied) + initialStored
      ≡ grossElectricalExport
        + (driverRecovered + (thermalBudget + (opticalEscaped + finalStored)))

open PVDrivenWorkWindow public

availableEnergy : PVDrivenWorkWindow -> Nat
availableEnergy r = (solarIncident r + driverSupplied r) + initialStored r

grossElectricalNoGreaterThanAllInputs :
  (r : PVDrivenWorkWindow) ->
  Bound._≤_ (grossElectricalExport r) (availableEnergy r)
grossElectricalNoGreaterThanAllInputs r =
  Bound.transportUpper
    (Bound.sym (energyBalance r))
    (Bound.≤-append (grossElectricalExport r)
      (driverRecovered r + (thermalBudget r + (opticalEscaped r + finalStored r))))

------------------------------------------------------------------------
-- Source-independent negative control: more pairs can mean less work.
-- Arbitrary toy voltage/energy quanta, NOT photovoltaic measurement.
------------------------------------------------------------------------

record ChargeWorkFixture : Set where
  constructor chargeWorkFixture
  field
    collectedPairs : Nat
    terminalVoltageCode : Nat
    exportedWorkCode : Nat
    accounted : collectedPairs * terminalVoltageCode ≡ exportedWorkCode

open ChargeWorkFixture public

moreCarriers : ChargeWorkFixture
moreCarriers = chargeWorkFixture 3 1 3 refl

morePower : ChargeWorkFixture
morePower = chargeWorkFixture 2 3 6 refl

pairsOfMorePowerNotGreater :
  Bound._≤_ (collectedPairs morePower) (collectedPairs moreCarriers)
pairsOfMorePowerNotGreater = Bound.s≤s (Bound.s≤s Bound.z≤n)

workOfMoreCarriersNotGreater :
  Bound._≤_ (exportedWorkCode moreCarriers) (exportedWorkCode morePower)
workOfMoreCarriersNotGreater =
  Bound.s≤s (Bound.s≤s (Bound.s≤s Bound.z≤n))
