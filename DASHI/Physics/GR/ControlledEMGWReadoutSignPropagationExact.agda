module DASHI.Physics.GR.ControlledEMGWReadoutSignPropagationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange
import DASHI.Physics.GR.ControlledEMGWExchangeFiniteReversalExact as Reversal

------------------------------------------------------------------------
-- SIGN PROPAGATION: EXCHANGE WORK -> EM FREQUENCY -> DELAYED PHASE
--
-- Sign convention:
--   positive work sign = energy delivered BY the EM field TO the GW;
--   negative work sign = energy delivered TO the EM field FROM the GW.
-- Therefore Delta E_EM = hbar Delta Omega carries the opposite sign from this
-- exchange-work convention.  Frequency and delayed optical phase then share
-- the same sign.
------------------------------------------------------------------------

data ReadoutSign : Set where
  positiveReadout : ReadoutSign
  zeroReadout : ReadoutSign
  negativeReadout : ReadoutSign

exchangeToWorkSign : Exchange.ExchangeSign → ReadoutSign
exchangeToWorkSign Exchange.emissionLike = positiveReadout
exchangeToWorkSign Exchange.absorptionLike = negativeReadout
exchangeToWorkSign Exchange.zeroExchange = zeroReadout

flipReadoutSign : ReadoutSign → ReadoutSign
flipReadoutSign positiveReadout = negativeReadout
flipReadoutSign negativeReadout = positiveReadout
flipReadoutSign zeroReadout = zeroReadout

frequencySignFromWorkSign : ReadoutSign → ReadoutSign
frequencySignFromWorkSign sign = flipReadoutSign sign

phaseSignFromFrequencySign : ReadoutSign → ReadoutSign
phaseSignFromFrequencySign sign = sign

emissionFrequencySignIsNegative :
  frequencySignFromWorkSign (exchangeToWorkSign Exchange.emissionLike)
  ≡ negativeReadout
emissionFrequencySignIsNegative = refl

absorptionFrequencySignIsPositive :
  frequencySignFromWorkSign (exchangeToWorkSign Exchange.absorptionLike)
  ≡ positiveReadout
absorptionFrequencySignIsPositive = refl

exchangeFlipCommutesWithWorkSign :
  ∀ sign →
  exchangeToWorkSign (Reversal.flipExchangeSign sign)
    ≡ flipReadoutSign (exchangeToWorkSign sign)
exchangeFlipCommutesWithWorkSign Exchange.emissionLike = refl
exchangeFlipCommutesWithWorkSign Exchange.absorptionLike = refl
exchangeFlipCommutesWithWorkSign Exchange.zeroExchange = refl

flipReadoutInvolutive :
  ∀ sign → flipReadoutSign (flipReadoutSign sign) ≡ sign
flipReadoutInvolutive positiveReadout = refl
flipReadoutInvolutive zeroReadout = refl
flipReadoutInvolutive negativeReadout = refl

reversalPropagatesToPhaseSign :
  ∀ reversal sign →
  phaseSignFromFrequencySign
    (frequencySignFromWorkSign
      (exchangeToWorkSign (Reversal.reversalActsOnSign reversal sign)))
  ≡
  flipReadoutSign
    (phaseSignFromFrequencySign
      (frequencySignFromWorkSign (exchangeToWorkSign sign)))
reversalPropagatesToPhaseSign Exchange.orthogonalPathExchange Exchange.emissionLike = refl
reversalPropagatesToPhaseSign Exchange.orthogonalPathExchange Exchange.absorptionLike = refl
reversalPropagatesToPhaseSign Exchange.orthogonalPathExchange Exchange.zeroExchange = refl
reversalPropagatesToPhaseSign Exchange.halfCyclePhaseExchange Exchange.emissionLike = refl
reversalPropagatesToPhaseSign Exchange.halfCyclePhaseExchange Exchange.absorptionLike = refl
reversalPropagatesToPhaseSign Exchange.halfCyclePhaseExchange Exchange.zeroExchange = refl
reversalPropagatesToPhaseSign Exchange.polarizationExchange Exchange.emissionLike = refl
reversalPropagatesToPhaseSign Exchange.polarizationExchange Exchange.absorptionLike = refl
reversalPropagatesToPhaseSign Exchange.polarizationExchange Exchange.zeroExchange = refl

record ReadoutSignBoundary : Set where
  constructor readout-sign-boundary
  field
    exchangeReversalPropagatesToWorkSign : Bool
    exchangeWorkSignOpposesEMFrequencySign : Bool
    frequencySignPropagatesToDelayedPhaseSign : Bool
    numericalCalibrationStillRequired : Bool
    signTheoremAloneDoesNotEstablishDetectability : Bool

canonicalReadoutSignBoundary : ReadoutSignBoundary
canonicalReadoutSignBoundary =
  readout-sign-boundary true true true true true
