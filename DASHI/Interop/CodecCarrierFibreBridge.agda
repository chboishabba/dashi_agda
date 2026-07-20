module DASHI.Interop.CodecCarrierFibreBridge where

open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using (TriTruth)
open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Codec.BalancedTritBitFibre using
  ( Sign
  ; positiveSign
  ; negativeSign
  ; TritFibre
  ; encodeFibre
  ; decodeFibre
  ; invertSign
  ; invertFibre
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
-- Reuse the canonical SSP trit carrier rather than creating a codec-local
-- signed ternary type.

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
-- The bridge intentionally leaves the zero fibre separate. Polarity exists
-- only after support has selected a non-zero trit, preserving the exact
-- support/sign quotient rather than assigning an arbitrary sign to zero.

signedPolarity : TritFibre → Set
signedPolarity f = SignedWitness f
  where
  data SignedWitness : TritFibre → Set where
    positiveWitness : SignedWitness (encodeFibre (decodeFibre (encodeFibre (decodeFibre f))))

-- A direct executable readout for consumers that already know they are on a
-- signed fibre.
signedFibrePolarity : Sign → SignPolarity
signedFibrePolarity = signToPolarity
