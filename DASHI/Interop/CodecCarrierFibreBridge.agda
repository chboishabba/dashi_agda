module DASHI.Interop.CodecCarrierFibreBridge where

open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using (TriTruth)
open import DASHI.Codec.BalancedTritBitFibre using
  ( Sign
  ; positiveSign
  ; negativeSign
  ; TritFibre
  ; encodeFibre
  ; decodeFibre
  ; invertSign
  )
open import DASHI.Foundations.Base369MobiusTransport using
  ( OrientationPolarity
  ; positive
  ; negative
  ; flipOrientationPolarity
  )
open import DASHI.Foundations.SSPTritCarrier using
  ( SSPTrit
  ; toTrit
  ; fromTrit
  ; toTriTruth
  )

------------------------------------------------------------------------
-- Canonical SSP trits and codec support/sign fibres are equivalent.

sspToFibre : SSPTrit → TritFibre
sspToFibre s = encodeFibre (toTrit s)

fibreToSSP : TritFibre → SSPTrit
fibreToSSP f = fromTrit (decodeFibre f)

fibreToSSP-sspToFibre : ∀ s → fibreToSSP (sspToFibre s) ≡ s
fibreToSSP-sspToFibre s
  rewrite DASHI.Codec.BalancedTritBitFibre.decode-encode (toTrit s)
        | DASHI.Foundations.SSPTritCarrier.fromTrit-toTrit s = refl

sspToFibre-fibreToSSP : ∀ f → sspToFibre (fibreToSSP f) ≡ f
sspToFibre-fibreToSSP f
  rewrite DASHI.Foundations.SSPTritCarrier.toTrit-fromTrit (decodeFibre f)
        | DASHI.Codec.BalancedTritBitFibre.encode-decode f = refl

sspTriPhase : SSPTrit → TriTruth
sspTriPhase = toTriTruth

------------------------------------------------------------------------
-- Reuse the established two-point orientation fibre. This does not identify
-- TritFibre with HexTruth: only the signed, non-zero fibre is transported.

SignPolarity : Set
SignPolarity = OrientationPolarity

signToPolarity : Sign → SignPolarity
signToPolarity positiveSign = positive
signToPolarity negativeSign = negative

polarityToSign : SignPolarity → Sign
polarityToSign positive = positiveSign
polarityToSign negative = negativeSign

polarityToSign-signToPolarity : ∀ s → polarityToSign (signToPolarity s) ≡ s
polarityToSign-signToPolarity positiveSign = refl
polarityToSign-signToPolarity negativeSign = refl

signToPolarity-polarityToSign : ∀ p → signToPolarity (polarityToSign p) ≡ p
signToPolarity-polarityToSign positive = refl
signToPolarity-polarityToSign negative = refl

signToPolarity-commutes-flip :
  ∀ s → signToPolarity (invertSign s) ≡
        flipOrientationPolarity (signToPolarity s)
signToPolarity-commutes-flip positiveSign = refl
signToPolarity-commutes-flip negativeSign = refl
