module DASHI.Physics.GR.SchutzholdEMGWSourceLawExact where

open import DASHI.Core.Prelude

import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange

------------------------------------------------------------------------
-- SCHUTZHOLD 2025 CONTROLLED EM <-> GW SOURCE LAW
--
-- Ralf Schuetzhold, "Stimulated Emission or Absorption of Gravitons by
-- Light", Phys. Rev. Lett. 135, 171501 (2025), DOI 10.1103/xd97-c6d7;
-- arXiv:2502.10221.
--
-- Source-shaped equations used below:
--   metric: ds^2 = dt^2 - (1+h) dx^2 - (1-h) dy^2 - dz^2        Eq. (2)
--   Hint = h int d^3r [ (dy Az)^2 - (dx Az)^2 ]                 Eq. (4)
--   dE/dt = hdot int d^3r < (dy Az)^2 - (dx Az)^2 >             Eq. (5)
--   Omega^2 = (1-h) Kx^2 + (1+h) Ky^2                           Eq. (7)
-- and, for pure x/y propagation, Delta Omega = +/- h Omega / 2,
-- Delta E = +/- h E / 2 per half-cycle.  A delayed equal-path section turns
-- opposite lasting frequency shifts into a growing relative phase.
--
-- This module formalises the routing/sign content only.  Numerical analysis,
-- renormalised operator expectations and dimensional normalization remain
-- supplied by physical receipts.
------------------------------------------------------------------------

data TransverseDirection : Set where
  xDirection : TransverseDirection
  yDirection : TransverseDirection

data GWHDerivativeSign : Set where
  hIncreasing : GWHDerivativeSign
  hStationary : GWHDerivativeSign
  hDecreasing : GWHDerivativeSign

data EnergyFlow : Set where
  emLosesEnergy : EnergyFlow
  noEnergyTransfer : EnergyFlow
  emGainsEnergy : EnergyFlow

energyFlow : GWHDerivativeSign → TransverseDirection → EnergyFlow
energyFlow hIncreasing xDirection = emLosesEnergy
energyFlow hIncreasing yDirection = emGainsEnergy
energyFlow hStationary xDirection = noEnergyTransfer
energyFlow hStationary yDirection = noEnergyTransfer
energyFlow hDecreasing xDirection = emGainsEnergy
energyFlow hDecreasing yDirection = emLosesEnergy

exchangeSign : EnergyFlow → Exchange.ExchangeSign
exchangeSign emLosesEnergy = Exchange.emissionLike
exchangeSign noEnergyTransfer = Exchange.zeroExchange
exchangeSign emGainsEnergy = Exchange.absorptionLike

swapDirection : TransverseDirection → TransverseDirection
swapDirection xDirection = yDirection
swapDirection yDirection = xDirection

flipHDerivativeSign : GWHDerivativeSign → GWHDerivativeSign
flipHDerivativeSign hIncreasing = hDecreasing
flipHDerivativeSign hStationary = hStationary
flipHDerivativeSign hDecreasing = hIncreasing

swapDirectionInvolutive :
  (direction : TransverseDirection) →
  swapDirection (swapDirection direction) ≡ direction
swapDirectionInvolutive xDirection = refl
swapDirectionInvolutive yDirection = refl

flipHDerivativeInvolutive :
  (sign : GWHDerivativeSign) →
  flipHDerivativeSign (flipHDerivativeSign sign) ≡ sign
flipHDerivativeInvolutive hIncreasing = refl
flipHDerivativeInvolutive hStationary = refl
flipHDerivativeInvolutive hDecreasing = refl

sourceDirectionSwapFlipsExchange :
  (sign : GWHDerivativeSign) →
  exchangeSign (energyFlow sign (swapDirection xDirection))
  ≡
  exchangeSign (energyFlow (flipHDerivativeSign sign) xDirection)
sourceDirectionSwapFlipsExchange hIncreasing = refl
sourceDirectionSwapFlipsExchange hStationary = refl
sourceDirectionSwapFlipsExchange hDecreasing = refl

sourceHalfCycleScheduleEmission :
  exchangeSign (energyFlow hIncreasing xDirection)
  ≡ Exchange.emissionLike
sourceHalfCycleScheduleEmission = refl

sourceHalfCycleScheduleEmissionSecondHalf :
  exchangeSign (energyFlow hDecreasing yDirection)
  ≡ Exchange.emissionLike
sourceHalfCycleScheduleEmissionSecondHalf = refl

sourceOppositeScheduleAbsorption :
  exchangeSign (energyFlow hIncreasing yDirection)
  ≡ Exchange.absorptionLike
sourceOppositeScheduleAbsorption = refl

sourceOppositeScheduleAbsorptionSecondHalf :
  exchangeSign (energyFlow hDecreasing xDirection)
  ≡ Exchange.absorptionLike
sourceOppositeScheduleAbsorptionSecondHalf = refl

data SourceEquation : Set where
  weakGWMetricEquation : SourceEquation
  electromagneticLagrangianEquation : SourceEquation
  interactionHamiltonianEquation : SourceEquation
  energyTransferEquation : SourceEquation
  wkbWaveEquation : SourceEquation
  dispersionEquation : SourceEquation
  pureDirectionFrequencyShiftEquation : SourceEquation
  halfCycleEnergyShiftEquation : SourceEquation
  delayedPhaseAccumulationEquation : SourceEquation

sourceEquationText : SourceEquation → String
sourceEquationText weakGWMetricEquation =
  "ds^2 = dt^2 - (1+h) dx^2 - (1-h) dy^2 - dz^2"
sourceEquationText electromagneticLagrangianEquation =
  "L = 1/2[(dt Az)^2 - (1-h)(dx Az)^2 - (1+h)(dy Az)^2]"
sourceEquationText interactionHamiltonianEquation =
  "H_int = h integral[(dy Az)^2 - (dx Az)^2] d^3r"
sourceEquationText energyTransferEquation =
  "d<E>/dt = hdot integral <(dy Az)^2 - (dx Az)^2> d^3r"
sourceEquationText wkbWaveEquation =
  "(dt^2 - (1-h) dx^2 - (1+h) dy^2) Az = 0"
sourceEquationText dispersionEquation =
  "Omega^2 = (1-h) Kx^2 + (1+h) Ky^2"
sourceEquationText pureDirectionFrequencyShiftEquation =
  "Delta Omega = +/- h Omega / 2 for pure x/y propagation"
sourceEquationText halfCycleEnergyShiftEquation =
  "Delta E = +/- h E / 2 per half-cycle"
sourceEquationText delayedPhaseAccumulationEquation =
  "lasting opposite frequency shifts accumulate relative phase on equal delayed paths"

record SchutzholdSourceBoundary : Set where
  constructor schutzhold-source-boundary
  field
    standardLinearisedGRCouplingUsed : Bool
    sourceProvidesInteractionHamiltonian : Bool
    sourceProvidesEnergyTransferLaw : Bool
    sourceProvidesWKBDispersionLaw : Bool
    sourceProvidesHalfCycleEnergyShift : Bool
    sourceProvidesDelayedPhaseStrategy : Bool
    sourceAloneProvesGravityQuantised : Bool
    sourceAloneProvesAntigravity : Bool

canonicalSchutzholdSourceBoundary : SchutzholdSourceBoundary
canonicalSchutzholdSourceBoundary =
  schutzhold-source-boundary true true true true true true false false
