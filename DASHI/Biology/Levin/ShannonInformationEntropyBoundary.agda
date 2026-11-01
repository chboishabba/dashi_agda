module DASHI.Biology.Levin.ShannonInformationEntropyBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Formula-level boundary for Shannon surprisal and entropy.
--
-- Real analysis, logarithms, probability normalization, and expectation are
-- supplied through witnesses.  No numerical entropy theorem is postulated.

record FiniteProbabilityModel : Set₁ where
  field
    Symbol : Set
    probabilityNumerator : Symbol → Nat
    probabilityDenominator : Nat
    normalized : Bool
    positiveOnSupport : Bool

record SurprisalWitness : Set₁ where
  field
    Event : Set
    probabilitySpecified : Event → Bool
    negativeLogBaseTwoSpecified : Event → Bool
    rareEventHasNoSmallerSurprisalWitness : Bool
    independentProductAddsSurprisalWitness : Bool

record ShannonEntropyWitness : Set₁ where
  field
    SourceSymbol : Set
    distributionNormalized : Bool
    surprisalDefinedOnSupport : Bool
    weightedExpectationDefined : Bool
    entropyNonnegativeWitness : Bool
    deterministicSourceHasZeroEntropyWitness : Bool
    uniformFiniteSourceMaximizesEntropyWitness : Bool

record NoiselessCodingTheoremBoundary : Set where
  field
    sourceClassSpecified : Bool
    codeClassPrefixFree : Bool
    lowerBoundProved : Bool
    nearAchievabilityProved : Bool
    blockLengthIndexed : Bool
    asymptoticQuantifiersExplicit : Bool
    finiteLengthOverheadExplicit : Bool
    interpretation : String

canonicalNoiselessCodingBoundary : NoiselessCodingTheoremBoundary
canonicalNoiselessCodingBoundary = record
  { sourceClassSpecified = true
  ; codeClassPrefixFree = true
  ; lowerBoundProved = false
  ; nearAchievabilityProved = false
  ; blockLengthIndexed = true
  ; asymptoticQuantifiersExplicit = true
  ; finiteLengthOverheadExplicit = true
  ; interpretation = "Entropy is the candidate lower bound on expected prefix-code length, but lower-bound and achievability directions remain separate theorem obligations"
  }

CompressionOutputLooksRandomImpliesOptimal : Bool
CompressionOutputLooksRandomImpliesOptimal = false

HighEntropyImpliesSemanticComplexity : Bool
HighEntropyImpliesSemanticComplexity = false
