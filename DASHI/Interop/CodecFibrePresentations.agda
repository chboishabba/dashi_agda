module DASHI.Interop.CodecFibrePresentations where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using
  ( HexTruth; TriTruth
  ; hex-0; hex-1; hex-2; hex-3; hex-4; hex-5
  )
open import DASHI.Core.Prelude using (_×_; _,_; proj₁)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
open import DASHI.Codec.BalancedTritBitFibre using
  ( TritFibre; zeroFibre; signedFibre
  ; encodeFibre; decodeFibre; invertFibre; supportBit
  ; decode-encode; encode-decode; encode-commutes-involution
  )
open import DASHI.Codec.DNAFirstFormalism using (Base; A; C; G; T; complement)
open import DASHI.Codec.DNACarrierFibre using
  ( BaseFibre; ChemicalPair; atPair; cgPair
  ; encodeBaseFibre; decodeBaseFibre; complementFibre
  ; decode-encode-base; encode-decode-base
  ; encodeBaseFibre-complement-equivariant
  )
open import DASHI.Foundations.Base369MobiusTransport using
  ( OrientationPolarity; positive; negative
  ; flipOrientationPolarity; mobiusTransport
  )
open import DASHI.Foundations.HexTruthPolarityFactor using
  ( hexTruthToFactor; hexFactorToTruth
  ; hexTruthToFactor-decodingRoundTrip
  ; hexFactorToTruth-encodingRoundTrip
  ; mobiusTransport-factors
  )
open import DASHI.Foundations.InvolutiveFibrePresentation

------------------------------------------------------------------------
-- Trit: quotient is zero/non-zero support; encoded fibre retains optional sign.

tritQuotientInvariant :
  ∀ t → supportBit (invertFibre (encodeFibre t)) ≡ supportBit (encodeFibre t)
tritQuotientInvariant neg = refl
tritQuotientInvariant zer = refl
tritQuotientInvariant pos = refl

tritFibrePresentation : InvolutiveFibrePresentation
tritFibrePresentation = record
  { Carrier = Trit
  ; Encoded = TritFibre
  ; Quotient = Bool
  ; encode = encodeFibre
  ; decode = decodeFibre
  ; carrierInvolution = inv
  ; encodedInvolution = invertFibre
  ; quotient = supportBit
  ; decodeEncode = decode-encode
  ; encodeDecode = encode-decode
  ; involutionEquivariant = encode-commutes-involution
  ; quotientInvariant = tritQuotientInvariant
  }

------------------------------------------------------------------------
-- DNA: quotient is A/T versus C/G; encoded fibre retains complement phase.

basePairProjection : BaseFibre → ChemicalPair
basePairProjection (q , p) = q

baseQuotientInvariant :
  ∀ b → basePairProjection (complementFibre (encodeBaseFibre b)) ≡
        basePairProjection (encodeBaseFibre b)
baseQuotientInvariant A = refl
baseQuotientInvariant C = refl
baseQuotientInvariant G = refl
baseQuotientInvariant T = refl

dnaFibrePresentation : InvolutiveFibrePresentation
dnaFibrePresentation = record
  { Carrier = Base
  ; Encoded = BaseFibre
  ; Quotient = ChemicalPair
  ; encode = encodeBaseFibre
  ; decode = decodeBaseFibre
  ; carrierInvolution = complement
  ; encodedInvolution = complementFibre
  ; quotient = basePairProjection
  ; decodeEncode = decode-encode-base
  ; encodeDecode = encode-decode-base
  ; involutionEquivariant = encodeBaseFibre-complement-equivariant
  ; quotientInvariant = baseQuotientInvariant
  }

------------------------------------------------------------------------
-- HexTruth: quotient is TriTruth; encoded fibre is orientation polarity.

HexFactor : Set
HexFactor = TriTruth × OrientationPolarity

flipHexFactor : HexFactor → HexFactor
flipHexFactor (t , p) = t , flipOrientationPolarity p

hexFactorDecode : HexFactor → HexTruth
hexFactorDecode (t , p) = hexFactorToTruth t p

hexQuotient : HexFactor → TriTruth
hexQuotient = proj₁

hexDecodeEncode : ∀ x → hexFactorDecode (hexTruthToFactor x) ≡ x
hexDecodeEncode = hexTruthToFactor-decodingRoundTrip

hexEncodeDecode : ∀ f → hexTruthToFactor (hexFactorDecode f) ≡ f
hexEncodeDecode (t , p) = hexFactorToTruth-encodingRoundTrip t p

hexQuotientInvariant :
  ∀ x → hexQuotient (flipHexFactor (hexTruthToFactor x)) ≡
        hexQuotient (hexTruthToFactor x)
hexQuotientInvariant hex-0 = refl
hexQuotientInvariant hex-1 = refl
hexQuotientInvariant hex-2 = refl
hexQuotientInvariant hex-3 = refl
hexQuotientInvariant hex-4 = refl
hexQuotientInvariant hex-5 = refl

hexFibrePresentation : InvolutiveFibrePresentation
hexFibrePresentation = record
  { Carrier = HexTruth
  ; Encoded = HexFactor
  ; Quotient = TriTruth
  ; encode = hexTruthToFactor
  ; decode = hexFactorDecode
  ; carrierInvolution = mobiusTransport
  ; encodedInvolution = flipHexFactor
  ; quotient = hexQuotient
  ; decodeEncode = hexDecodeEncode
  ; encodeDecode = hexEncodeDecode
  ; involutionEquivariant = mobiusTransport-factors
  ; quotientInvariant = hexQuotientInvariant
  }
