module DASHI.Physics.GR.ControlledEMGWReadoutSignPropagationExact where

open import DASHI.Core.Prelude

import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange
import DASHI.Physics.GR.ControlledEMGWExchangeFiniteReversalExact as Reversal

------------------------------------------------------------------------
-- SIGN PROPAGATION: WORK -> FREQUENCY -> DELAYED PHASE
--
-- This is deliberately only the sign layer.  Numerical normalization still
-- belongs to the physical work/frequency/phase receipts in the interaction
-- carrier.  Once those calibrated maps preserve orientation, the controlled
-- reversal propagates all the way to the interferometric phase sign.
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
frequencySignFromWorkSign sign = sign

phaseSignFromFrequencySign : ReadoutSign → ReadoutSign
phaseSignFromFrequencySign sign = sign

exchangeFlipCommutesWithWorkSign :
  ∀ sign →
  exchangeToWorkSign (Reversal.flipExchangeSign sign)
    ≡ flipReadoutSign (exchangeToWorkSign sign)
exchangeFlipCommutesWithWorkSign Exchange.emissionLike = refl
exchangeFlipCommutesWithWorkSign Exchange.absorptionLike = refl
exchangeFlipCommutesWithWorkSign Exchange.zeroExchange = refl

reversalPropagatesToPhaseSign :
  ∀ reversal sign →
  phaseSignFromFrequencySign
    (frequencySignFromWorkSign
      (exchangeToWorkSign (Reversal.reversalActsOnSign reversal sign)))
  ≡
  flipReadoutSign
    (phaseSignFromFrequencySign
      (frequencySignFromWorkSign (exchangeToWorkSign sign)))
reversalPropagatesToPhaseSign Exchange.orthogonalPathExchange sign =
  exchangeFlipCommutesWithWorkSign sign
reversalPropagatesToPhaseSign Exchange.halfCyclePhaseExchange sign =
  exchangeFlipCommutesWithWorkSign sign
reversalPropagatesToPhaseSign Exchange.polarizationExchange sign =
  exchangeFlipCommutesWithWorkSign sign

record ReadoutSignBoundary : Set where
  constructor readout-sign-boundary
  field
    exchangeReversalPropagatesToWorkSign : Bool
    workSignPropagatesToFrequencySign : Bool
    frequencySignPropagatesToDelayedPhaseSign : Bool
    numericalCalibrationStillRequired : Bool
    signTheoremAloneDoesNotEstablishDetectability : Bool

canonicalReadoutSignBoundary : ReadoutSignBoundary
canonicalReadoutSignBoundary =
  readout-sign-boundary true true true true true
