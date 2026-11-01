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
  ; decode-encode
  ; encode-decode
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
  ; toTrit-fromTrit
  ; fromTrit-toTrit
  ; toTriTruth
  )

------------------------------------------------------------------------
-- Reuse the canonical SSP trit carrier rather than creating a codec-local
-- signed ternary type.

sspToFibre : SSPTrit → TritFibre
sspToFibre s = encodeFibre (toTrit s)

fibreToSSP : TritFibre → SSPTrit
fibreToSSP f = fromTrit (decodeFibre f)

fibreToSSP-sspToFibre : ∀ s → fibreToSSP (sspToFibre s) ≡ s
fibreToSSP-sspToFibre s
  rewrite decode-encode (toTrit s)
        | fromTrit-toTrit s = refl

sspToFibre-fibreToSSP : ∀ f → sspToFibre (fibreToSSP f) ≡ f
sspToFibre-fibreToSSP f
  rewrite toTrit-fromTrit (decodeFibre f)
        | encode-decode f = refl

sspTriPhase : SSPTrit → TriTruth
sspTriPhase = toTriTruth

------------------------------------------------------------------------
-- The sign fibre reuses the orientation polarity already used by the
-- HexTruth ≅ TriTruth × Polarity factorisation. This is a structural bridge:
-- it identifies the same two-point involutive fibre, without identifying a
-- TritFibre with HexTruth or manufacturing a six-state codec semantics.

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

------------------------------------------------------------------------
-- Zero remains outside OrientationPolarity. A polarity value is requested
-- only after the support quotient has selected a signed fibre; no arbitrary
-- sign is assigned to the neutral trit.

signedFibrePolarity : Sign → SignPolarity
signedFibrePolarity = signToPolarity
