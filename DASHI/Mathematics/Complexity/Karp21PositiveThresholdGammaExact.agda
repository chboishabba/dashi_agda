module DASHI.Mathematics.Complexity.Karp21PositiveThresholdGammaExact where

------------------------------------------------------------------------
-- KARP WEIGHTED MAX CUT: POSITIVE ℤ THRESHOLD -> POSITIVE GAMMA NAT.
--
-- Original Cut.WeightedCutGraph.thresholdPositive is a pair
--    0 ≤ W  and  W ≢ 0.
-- The literal GraphWord decoder rejects gamma(0) and accepts only
-- gamma(suc k). This module source-writes the exact bridge for the
-- original threshold and the original gamma(n+1) numeral codec.
--
-- No invented threshold marker; signed weights remain unrestricted.
-- This is source-written and Agda-kernel-unverified integration code.
-- Karp 1972; DASHI Karp21ScaledThresholdExact and gamma owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.List.Base using (_++_)
open import Data.Maybe.Base using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥-elim)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21ScaledThresholdExact as Threshold
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Encode
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Decode
import DASHI.Mathematics.Complexity.Karp21GammaBinaryRoundTripExact as Gamma

positiveThresholdIsSuccessor :
  (value : ℤ) →
  Threshold.PositiveThreshold value →
  Σ Nat (λ k → value ≡ + (suc k))
positiveThresholdIsSuccessor (+ zero) (nonnegative , nonzero) =
  ⊥-elim (nonzero refl)
positiveThresholdIsSuccessor (+ (suc k)) positive =
  k , refl
positiveThresholdIsSuccessor (-[1+ k ]) (() , nonzero)

positiveThresholdMagnitudeSuccessor :
  (value : ℤ) →
  Threshold.PositiveThreshold value →
  Σ Nat (λ k → ∣ value ∣ ≡ suc k)
positiveThresholdMagnitudeSuccessor value positive
  with positiveThresholdIsSuccessor value positive
... | k , refl = k , refl

readPositiveThresholdGammaSuffix :
  (value : ℤ)
  (positive : Threshold.PositiveThreshold value)
  (suffix : Word.BitWord) →
  Σ Nat (λ k →
    (value ≡ + (suc k))
    × (Decode.readGamma
        (Encode.encodeGammaNat (∣ value ∣) ++ suffix)
        ≡ just (suc k , suffix)))
readPositiveThresholdGammaSuffix value positive suffix
  with positiveThresholdIsSuccessor value positive
... | k , refl =
  k , (refl , Gamma.gammaReadEncodeSuffix (suc k) suffix)
