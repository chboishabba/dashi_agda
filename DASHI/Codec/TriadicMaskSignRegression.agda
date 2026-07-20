module DASHI.Codec.TriadicMaskSignRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Codec.TriadicMaskSign
open import DASHI.Codec.TriadicGlobalInversionFold
open import DASHI.Codec.RANSMaskSignModel
open import DASHI.Algebra.Trit using (Trit; zer)
  renaming (neg to algebraNeg; pos to algebraPos)
open import DASHI.Codec.TriadicMaskSignFactorization
open import DASHI.Codec.TriadicMaskSignEntropyContract
open import DASHI.Codec.TriadicMaskSignSSPBridge
open import DASHI.Foundations.SSPTritCarrier
  using (sspNegOne; sspZero; sspPosOne)

------------------------------------------------------------------------
-- Compact import/regression surface for the exact finite codec tranche.
------------------------------------------------------------------------

zeroTriple : Trit3
zeroTriple = tri3 zero zero zero

mixedTriple : Trit3
mixedTriple = tri3 neg zero pos

fullTriple : Trit3
fullTriple = tri3 pos neg pos

zero-mask-roundtrip : decode3 (encode3 zeroTriple) ≡ zeroTriple
zero-mask-roundtrip = refl

mixed-mask-roundtrip : decode3 (encode3 mixedTriple) ≡ mixedTriple
mixed-mask-roundtrip = refl

full-mask-roundtrip : decode3 (encode3 fullTriple) ≡ fullTriple
full-mask-roundtrip = refl

mixed-fold-roundtrip : decodeFold14 (encodeFold14 mixedTriple) ≡ mixedTriple
mixed-fold-roundtrip = refl

cold-mask-table-total :
  maskFrequencyTotal (RANSModelContract.maskTable coldStartModel) ≡ TotalFrequency
cold-mask-table-total = RANSModelContract.maskNormalized coldStartModel

cold-sign-table-total :
  signFrequencyTotal (RANSModelContract.signTable coldStartModel) ≡ TotalFrequency
cold-sign-table-total = RANSModelContract.signNormalized coldStartModel

------------------------------------------------------------------------
-- Existing factorisation-layer normalization witnesses.

negativeDigitRoundtrip : decodeTrit (encodeTrit algebraNeg) ≡ algebraNeg
negativeDigitRoundtrip = refl

zeroDigitRoundtrip : decodeTrit (encodeTrit zer) ≡ zer
zeroDigitRoundtrip = refl

positiveDigitRoundtrip : decodeTrit (encodeTrit algebraPos) ≡ algebraPos
positiveDigitRoundtrip = refl

sparseTriple : Triple Trit
sparseTriple = triple algebraNeg zer algebraPos

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
  maskOf (encodeTriple (triple algebraNeg algebraPos algebraNeg)) ≡ mask111
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
