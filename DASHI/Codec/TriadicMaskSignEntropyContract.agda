module DASHI.Codec.TriadicMaskSignEntropyContract where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Codec.TriadicMaskSignFactorization
  using (Mask3; Sign)

------------------------------------------------------------------------
-- Typed specification boundary for source probabilities and ideal lengths.
--
-- The exact support/sign bijection is proved in
-- TriadicMaskSignFactorization.  Shannon entropy and finite-precision rANS
-- correctness require a probability/real-analysis and machine-arithmetic
-- development that is not currently canonical in this repository.  Those
-- obligations are therefore explicit fields here, not promoted theorems.

record EntropyModel : Set₁ where
  field
    Rate : Set
    zeroRate : Rate
    _+R_ : Rate → Rate → Rate
    _*R_ : Rate → Rate → Rate

    maskEntropy : Mask3 → Rate
    signEntropy : Sign → Rate
    activityDensity : Rate

    conditionalSignRate : Rate
    conditionalSignRate-law :
      conditionalSignRate ≡ activityDensity *R signEntropy positive

    planeRate : Rate
    planeRate-law :
      planeRate ≡ maskEntropy mask000 +R conditionalSignRate

open EntropyModel public

------------------------------------------------------------------------
-- Production rANS interface contract.

data AlphabetKind : Set where
  maskAlphabet : AlphabetKind
  signAlphabet : AlphabetKind

data StreamKind : Set where
  maskStream : StreamKind
  gatedSignStream : StreamKind

record RANSTableContract : Set where
  field
    alphabet : AlphabetKind
    alphabetSize : Nat
    totalFrequency : Nat
    frequenciesArePositive : Bool
    frequenciesSumToTotal : Bool

open RANSTableContract public

maskTable4096 : RANSTableContract
maskTable4096 = record
  { alphabet = maskAlphabet
  ; alphabetSize = 8
  ; totalFrequency = 4096
  ; frequenciesArePositive = true
  ; frequenciesSumToTotal = true
  }

signTable4096 : RANSTableContract
signTable4096 = record
  { alphabet = signAlphabet
  ; alphabetSize = 2
  ; totalFrequency = 4096
  ; frequenciesArePositive = true
  ; frequenciesSumToTotal = true
  }

record MaskSignRANSContract : Set where
  field
    maskTable : RANSTableContract
    signTable : RANSTableContract

    maskAlphabet-is-eight : alphabetSize maskTable ≡ 8
    signAlphabet-is-two : alphabetSize signTable ≡ 2
    sharedTotalFrequency :
      totalFrequency maskTable ≡ totalFrequency signTable
    totalFrequency-is-4096 : totalFrequency maskTable ≡ 4096

    signEmissionIsGated : Bool
    perPlaneTables : Bool
    optionalSingleContextBit : Bool

    implementationClaimBoundary : String

open MaskSignRANSContract public

canonicalMaskSignRANSContract : MaskSignRANSContract
canonicalMaskSignRANSContract = record
  { maskTable = maskTable4096
  ; signTable = signTable4096
  ; maskAlphabet-is-eight = refl
  ; signAlphabet-is-two = refl
  ; sharedTotalFrequency = refl
  ; totalFrequency-is-4096 = refl
  ; signEmissionIsGated = true
  ; perPlaneTables = true
  ; optionalSingleContextBit = true
  ; implementationClaimBoundary =
      "Typed production contract only: this module does not prove finite-precision rANS normalization, coder roundtrip, or empirical optimality."
  }
