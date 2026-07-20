module DASHI.Foundations.InvolutiveTernaryExistingSpineBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.InvolutiveTernaryDynamics as ITD

------------------------------------------------------------------------
-- Existing-spine adapter.
--
-- This module does not introduce another trit carrier.  It proves that the
-- established SSP carrier is an instance of the generic involutive carrier
-- and that the new support quotient agrees with the SSP neutrality surface.

sspι : SSP.SSPTrit → SSP.SSPTrit
sspι s = SSP.fromTrit (Trit.inv (SSP.toTrit s))

sspι-neg : sspι SSP.sspNegOne ≡ SSP.sspPosOne
sspι-neg = refl

sspι-zero : sspι SSP.sspZero ≡ SSP.sspZero
sspι-zero = refl

sspι-pos : sspι SSP.sspPosOne ≡ SSP.sspNegOne
sspι-pos = refl

sspι-involutive : ∀ s → sspι (sspι s) ≡ s
sspι-involutive SSP.sspNegOne = refl
sspι-involutive SSP.sspZero = refl
sspι-involutive SSP.sspPosOne = refl

sspInvolutiveCarrier : ITD.InvolutiveCarrier
sspInvolutiveCarrier = record
  { Carrier = SSP.SSPTrit
  ; ι = sspι
  ; ι-involutive = sspι-involutive
  }

sspSupport : SSP.SSPTrit → Bool
sspSupport s = ITD.support (SSP.toTrit s)

sspSupport-neg : sspSupport SSP.sspNegOne ≡ true
sspSupport-neg = refl

sspSupport-zero : sspSupport SSP.sspZero ≡ false
sspSupport-zero = refl

sspSupport-pos : sspSupport SSP.sspPosOne ≡ true
sspSupport-pos = refl

sspSupport-invariant : ∀ s → sspSupport (sspι s) ≡ sspSupport s
sspSupport-invariant SSP.sspNegOne = refl
sspSupport-invariant SSP.sspZero = refl
sspSupport-invariant SSP.sspPosOne = refl

-- The existing SSP neutrality classifier and the generic support quotient are
-- complementary views of the same carrier: neutral maps to inactive, while
-- both polarities map to active.

supportAgreesWithSSPNeutrality : ∀ s →
  sspSupport s ≡
  (case SSP.sspTritIsNeutral s of λ where
    true → false
    false → true)
supportAgreesWithSSPNeutrality SSP.sspNegOne = refl
supportAgreesWithSSPNeutrality SSP.sspZero = refl
supportAgreesWithSSPNeutrality SSP.sspPosOne = refl

-- Round-trip compatibility records that inversion is transported through the
-- already-proved SSP <-> canonical Trit equivalence rather than redefined.

sspι-toTrit : ∀ s → SSP.toTrit (sspι s) ≡ Trit.inv (SSP.toTrit s)
sspι-toTrit SSP.sspNegOne = refl
sspι-toTrit SSP.sspZero = refl
sspι-toTrit SSP.sspPosOne = refl

record ExistingSpineBridgeReceipt : Set where
  constructor receipt
  field
    sspCarrierIsGenericInvolutive : ITD.InvolutiveCarrier
    neutralIsFixed : sspι SSP.sspZero ≡ SSP.sspZero
    supportIsMirrorInvariant : ∀ s → sspSupport (sspι s) ≡ sspSupport s
    transportedInversion : ∀ s → SSP.toTrit (sspι s) ≡ Trit.inv (SSP.toTrit s)

existingSpineBridgeReceipt : ExistingSpineBridgeReceipt
existingSpineBridgeReceipt =
  receipt
    sspInvolutiveCarrier
    sspι-zero
    sspSupport-invariant
    sspι-toTrit
