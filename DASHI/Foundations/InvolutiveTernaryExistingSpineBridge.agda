module DASHI.Foundations.InvolutiveTernaryExistingSpineBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.InvolutiveTernaryDynamics as ITD

------------------------------------------------------------------------
-- The established SSP carrier is an instance of the generic involutive
-- carrier.  Inversion is transported through the already proved SSP/Trit
-- equivalence; no parallel trit representation is introduced here.

sspι : SSP.SSPTrit → SSP.SSPTrit
sspι s = SSP.fromTrit (Trit.inv (SSP.toTrit s))

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

sspSupport-invariant : ∀ s → sspSupport (sspι s) ≡ sspSupport s
sspSupport-invariant SSP.sspNegOne = refl
sspSupport-invariant SSP.sspZero = refl
sspSupport-invariant SSP.sspPosOne = refl

notBool : Bool → Bool
notBool false = true
notBool true = false

supportAgreesWithSSPNeutrality : ∀ s →
  sspSupport s ≡ notBool (SSP.sspTritIsNeutral s)
supportAgreesWithSSPNeutrality SSP.sspNegOne = refl
supportAgreesWithSSPNeutrality SSP.sspZero = refl
supportAgreesWithSSPNeutrality SSP.sspPosOne = refl

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
    supportIsDerivedNeutrality : ∀ s →
      sspSupport s ≡ notBool (SSP.sspTritIsNeutral s)
    transportedInversion : ∀ s →
      SSP.toTrit (sspι s) ≡ Trit.inv (SSP.toTrit s)

existingSpineBridgeReceipt : ExistingSpineBridgeReceipt
existingSpineBridgeReceipt =
  receipt
    sspInvolutiveCarrier
    refl
    sspSupport-invariant
    supportAgreesWithSSPNeutrality
    sspι-toTrit
