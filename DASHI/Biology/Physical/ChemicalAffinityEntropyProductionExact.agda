module DASHI.Biology.Physical.ChemicalAffinityEntropyProductionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
-- Jeremy L. England, "Statistical physics of self-replication",
-- The Journal of Chemical Physics 139 (2013), 121923.
-- DOI: 10.1063/1.4818538.
--
-- DASHI CONTRIBUTION
-- A finite exact affinity/throughput regression.  Molar free-energy drop is
-- represented by a truncated nonnegative affinity in a declared forward
-- regime; multiplying by molar flow gives a power-scale dissipation numerator.
-- Division by temperature, logarithmic chemical potentials, and calibrated
-- kinetics remain with the thermodynamic owner rather than being faked here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Physics.Units.SI as SI
import DASHI.Biology.Physical.SIBiologyDimensionsExact as BioSI
import DASHI.Physics.Laws.ThermodynamicStatisticalLaws as Thermo

forwardAffinityMagnitude : Nat → Nat → Nat
forwardAffinityMagnitude reactantPotential productPotential =
  reactantPotential ∸ productPotential

dissipatedPowerMagnitude : Nat → Nat → Nat
dissipatedPowerMagnitude molarFlow affinity = molarFlow * affinity

canonicalReactantPotential : Nat
canonicalReactantPotential = 7

canonicalProductPotential : Nat
canonicalProductPotential = 3

canonicalMolarFlow : Nat
canonicalMolarFlow = 2

canonicalAffinityIsFour :
  forwardAffinityMagnitude canonicalReactantPotential canonicalProductPotential ≡ 4
canonicalAffinityIsFour = refl

canonicalDissipatedPowerIsEight :
  dissipatedPowerMagnitude canonicalMolarFlow
    (forwardAffinityMagnitude canonicalReactantPotential canonicalProductPotential)
  ≡ 8
canonicalDissipatedPowerIsEight = refl

zeroAffinityProducesZeroPower :
  (flow potential : Nat) →
  dissipatedPowerMagnitude flow (forwardAffinityMagnitude potential potential) ≡ 0
zeroAffinityProducesZeroPower flow potential
  rewrite ∸-refl potential = *-zeroʳ flow

record ChemicalDissipationSISignature : Set₁ where
  field
    chemicalPotential : Set
    molarFlow : Set
    dissipatedPower : Set
    entropyFlowRate : Set

    potentialIsMolarEnergy :
      chemicalPotential ≡ SI.Quantity SI.MolarEnergy SI.unitScale
    molarFlowIsSI :
      molarFlow ≡ SI.Quantity BioSI.MolarFlowRate SI.unitScale
    powerIsSI :
      dissipatedPower ≡ SI.Quantity SI.Power SI.unitScale
    entropyRateIsSI :
      entropyFlowRate ≡ SI.Quantity BioSI.EntropyFlowRate SI.unitScale

open ChemicalDissipationSISignature public

canonicalChemicalDissipationSISignature : ChemicalDissipationSISignature
canonicalChemicalDissipationSISignature = record
  { chemicalPotential = SI.Quantity SI.MolarEnergy SI.unitScale
  ; molarFlow = SI.Quantity BioSI.MolarFlowRate SI.unitScale
  ; dissipatedPower = SI.Quantity SI.Power SI.unitScale
  ; entropyFlowRate = SI.Quantity BioSI.EntropyFlowRate SI.unitScale
  ; potentialIsMolarEnergy = refl
  ; molarFlowIsSI = refl
  ; powerIsSI = refl
  ; entropyRateIsSI = refl
  }
