module DASHI.Physics.GR.ControlledEMGWExchangeFiniteReversalExact where

open import DASHI.Core.Prelude

import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange

------------------------------------------------------------------------
-- FINITE SIGN/REVERSAL ALGEBRA FOR CONTROLLED EM <-> GW EXCHANGE
--
-- This closes the purely combinatorial part of the reversal lane.  It does
-- not assert that a physical apparatus realizes these reversals; that remains
-- a receipt in the physical interaction carrier.  Once a concrete setup has
-- been welded to these three controls, the opposite-sign conclusions below
-- are definitional/machine-checkable rather than prose assumptions.
------------------------------------------------------------------------

flipExchangeSign : Exchange.ExchangeSign → Exchange.ExchangeSign
flipExchangeSign Exchange.emissionLike = Exchange.absorptionLike
flipExchangeSign Exchange.absorptionLike = Exchange.emissionLike
flipExchangeSign Exchange.zeroExchange = Exchange.zeroExchange

flipExchangeSignInvolutive :
  ∀ sign → flipExchangeSign (flipExchangeSign sign) ≡ sign
flipExchangeSignInvolutive Exchange.emissionLike = refl
flipExchangeSignInvolutive Exchange.absorptionLike = refl
flipExchangeSignInvolutive Exchange.zeroExchange = refl

reversalActsOnSign :
  Exchange.ExchangeReversal → Exchange.ExchangeSign → Exchange.ExchangeSign
reversalActsOnSign Exchange.orthogonalPathExchange = flipExchangeSign
reversalActsOnSign Exchange.halfCyclePhaseExchange = flipExchangeSign
reversalActsOnSign Exchange.polarizationExchange = flipExchangeSign

orthogonalPathReversesEmission :
  reversalActsOnSign Exchange.orthogonalPathExchange Exchange.emissionLike
    ≡ Exchange.absorptionLike
orthogonalPathReversesEmission = refl

orthogonalPathReversesAbsorption :
  reversalActsOnSign Exchange.orthogonalPathExchange Exchange.absorptionLike
    ≡ Exchange.emissionLike
orthogonalPathReversesAbsorption = refl

halfCycleReversesEmission :
  reversalActsOnSign Exchange.halfCyclePhaseExchange Exchange.emissionLike
    ≡ Exchange.absorptionLike
halfCycleReversesEmission = refl

polarizationReversesEmission :
  reversalActsOnSign Exchange.polarizationExchange Exchange.emissionLike
    ≡ Exchange.absorptionLike
polarizationReversesEmission = refl

reversalPreservesZero :
  ∀ reversal →
  reversalActsOnSign reversal Exchange.zeroExchange ≡ Exchange.zeroExchange
reversalPreservesZero Exchange.orthogonalPathExchange = refl
reversalPreservesZero Exchange.halfCyclePhaseExchange = refl
reversalPreservesZero Exchange.polarizationExchange = refl

doubleReversalRestoresSign :
  ∀ reversal sign →
  reversalActsOnSign reversal (reversalActsOnSign reversal sign) ≡ sign
doubleReversalRestoresSign Exchange.orthogonalPathExchange sign =
  flipExchangeSignInvolutive sign
doubleReversalRestoresSign Exchange.halfCyclePhaseExchange sign =
  flipExchangeSignInvolutive sign
doubleReversalRestoresSign Exchange.polarizationExchange sign =
  flipExchangeSignInvolutive sign

record FiniteReversalBoundary : Set where
  constructor finite-reversal-boundary
  field
    orthogonalPathEncodedAsSignInvolution : Bool
    halfCycleEncodedAsSignInvolution : Bool
    polarizationEncodedAsSignInvolution : Bool
    zeroExchangeRemainsZeroUnderControlReversal : Bool
    physicalRealizationStillRequiresSameObjectReceipt : Bool

canonicalFiniteReversalBoundary : FiniteReversalBoundary
canonicalFiniteReversalBoundary =
  finite-reversal-boundary true true true true true
