module DASHI.Codec.TriadicMaskSignRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Algebra.Trit using (neg; zer; pos)
open import DASHI.Codec.TriadicMaskSignFactorization
open import DASHI.Codec.TriadicMaskSignEntropyContract
open import DASHI.Codec.TriadicMaskSignSSPBridge
open import DASHI.Foundations.SSPTritCarrier
  using (sspNegOne; sspZero; sspPosOne)

------------------------------------------------------------------------
-- Executable normalization witnesses for the exact algebraic layer.

negativeDigitRoundtrip : decodeTrit (encodeTrit neg) ≡ neg
negativeDigitRoundtrip = refl

zeroDigitRoundtrip : decodeTrit (encodeTrit zer) ≡ zer
zeroDigitRoundtrip = refl

positiveDigitRoundtrip : decodeTrit (encodeTrit pos) ≡ pos
positiveDigitRoundtrip = refl

sparseTriple : Triple _
sparseTriple = triple neg zer pos

sparseTripleMask : maskOf (encodeTriple sparseTriple) ≡ mask101
sparseTripleMask = refl

sparseTripleActiveCount : activeCount (encodeTriple sparseTriple) ≡ 2
sparseTripleActiveCount = refl

sparseTripleRoundtrip : decodeTriple (encodeTriple sparseTriple) ≡ sparseTriple
sparseTripleRoundtrip = refl

allInactiveMask :
  maskOf (encodeTriple (triple zer zer zer)) ≡ mask000
allInactiveMask = refl

allActiveMask :
  maskOf (encodeTriple (triple neg pos neg)) ≡ mask111
allActiveMask = refl

stateCountRegression : maskSignStateCount ≡ 27
stateCountRegression = maskSignStateCount-is-27

sspNegativeRoundtrip : decodeSSPTrit (encodeSSPTrit sspNegOne) ≡ sspNegOne
sspNegativeRoundtrip = refl

sspZeroRoundtrip : decodeSSPTrit (encodeSSPTrit sspZero) ≡ sspZero
sspZeroRoundtrip = refl

sspPositiveRoundtrip : decodeSSPTrit (encodeSSPTrit sspPosOne) ≡ sspPosOne
sspPositiveRoundtrip = refl

maskAlphabetRegression :
  alphabetSize (maskTable canonicalMaskSignRANSContract) ≡ 8
maskAlphabetRegression = refl

signAlphabetRegression :
  alphabetSize (signTable canonicalMaskSignRANSContract) ≡ 2
signAlphabetRegression = refl

frequencyRegression :
  totalFrequency (maskTable canonicalMaskSignRANSContract) ≡ 4096
frequencyRegression = refl
