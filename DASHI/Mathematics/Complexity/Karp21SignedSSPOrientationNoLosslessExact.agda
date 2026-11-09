module DASHI.Mathematics.Complexity.Karp21SignedSSPOrientationNoLosslessExact where

------------------------------------------------------------------------
-- Signed SSP / FRACTRAN reuse against ORIGINAL N21 signed binary tokens.
--
-- The orientation of an SSP valuation is a valid polarity projection.
-- It is not a lossless numerical encoding of arbitrary signed Karp
-- weights. In particular, two distinct positive binary magnitudes
-- have identical orientations. This noninjectivity is proved below.
--
-- Preserve Karp's bit-native signed ledger for executable arithmetic.
-- Using the SSP program or Nat exponents as the runtime requires an
-- independently proved word codec, simulation and polynomial clock.
--
-- Historical attribution: Conway's FRACTRAN; original DASHI SSP weave
-- and original E20/N21 signed gamma machinery.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Binary

-- A finite three-orientation projection, not a numerical conversion.
binarySignOrientation :
  Binary.SignedMagnitudeBits → SSP.FibreOrientation
binarySignOrientation (Binary.positive _) = SSP.forwardOrientation
binarySignOrientation (Binary.negative _) = SSP.inverseOrientation

-- The selected SSP machinery agrees on the sign-only interpretation.
binarySignAsSSPMultiplicity :
  Binary.SignedMagnitudeBits → SSP.SignedMultiplicity
binarySignAsSSPMultiplicity (Binary.positive _) =
  SSP.positiveMultiplicity 0
binarySignAsSSPMultiplicity (Binary.negative _) =
  SSP.negativeMultiplicity 0

binaryOrientationIsSSPOrientation :
  (w : Binary.SignedMagnitudeBits) →
  binarySignOrientation w
  ≡ SSP.orientationOfMultiplicity (binarySignAsSSPMultiplicity w)
binaryOrientationIsSSPOrientation (Binary.positive _) = refl
binaryOrientationIsSSPOrientation (Binary.negative _) = refl

flipBinarySign :
  Binary.SignedMagnitudeBits → Binary.SignedMagnitudeBits
flipBinarySign (Binary.positive magnitude) = Binary.negative magnitude
flipBinarySign (Binary.negative magnitude) = Binary.positive magnitude

flipBinaryInvolutive :
  (w : Binary.SignedMagnitudeBits) → flipBinarySign (flipBinarySign w) ≡ w
flipBinaryInvolutive (Binary.positive _) = refl
flipBinaryInvolutive (Binary.negative _) = refl

flipMatchesSSPNegation :
  (w : Binary.SignedMagnitudeBits) →
  binarySignOrientation (flipBinarySign w)
    ≡ SSP.orientationOfMultiplicity
        (SSP.negateMultiplicity (binarySignAsSSPMultiplicity w))
flipMatchesSSPNegation (Binary.positive _) = refl
flipMatchesSSPNegation (Binary.negative _) = refl

-- Concrete collision: two different binary payloads are identified
-- by the exact original signed SSP orientation projection.
zeroAndOneSameSSPOrientation :
  binarySignOrientation (Binary.positive [])
    ≡ binarySignOrientation (Binary.positive (true ∷ []))
zeroAndOneSameSSPOrientation = refl

zeroAndOneDifferentSignedTokens :
  Binary.positive [] ≡ Binary.positive (true ∷ []) → ⊥
zeroAndOneDifferentSignedTokens ()

-- Therefore no decoder from orientation *alone* can reconstruct all
-- original signed binary tokens. This rules out using sign only as a
-- lossless N21 verifier input or as a replacement for signed score.
noLosslessOrientationDecoder :
  (decode : SSP.FibreOrientation → Binary.SignedMagnitudeBits) →
  ((w : Binary.SignedMagnitudeBits) →
    decode (binarySignOrientation w) ≡ w) →
  ⊥
noLosslessOrientationDecoder decode roundtrip =
  zeroAndOneDifferentSignedTokens
    (trans
      (sym (roundtrip (Binary.positive [])))
      (roundtrip (Binary.positive (true ∷ []))))
