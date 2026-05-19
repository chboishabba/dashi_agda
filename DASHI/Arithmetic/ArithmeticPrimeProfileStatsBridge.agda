module DASHI.Arithmetic.ArithmeticPrimeProfileStatsBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Statistics.Vec15Descriptive using
  ( PrimeCarrier15
  ; sum15
  ; range15
  ; countNonZero15
  )
open import DASHI.Statistics.PrimeProfileStats using
  ( PrimeProfileStats
  ; primeProfileStats
  ; primeProfileWeights
  ; primeProfileScore
  )
open import DASHI.Statistics.PrimeProfileStatsSuite using
  ( PrimeProfileStatsSuite
  ; primeProfileStatsSuite
  ; PrimeProfileRobustStats
  ; PrimeProfileInferenceStats
  ; primeProfileRobustStats
  ; primeProfileInferenceStats
  )

------------------------------------------------------------------------
-- Bridge from an arithmetic-origin 15-lane carrier into the existing
-- prime-profile diagnostics.
--
-- The arithmetic-origin profile is already the repo-native 15-lane Nat
-- carrier, so the bridge packages it directly into the existing stats
-- record and suite while keeping the surface deterministic and thin.

record ArithmeticPrimeProfileStatsBridge : Set₁ where
  field
    arithmeticCarrier : PrimeCarrier15

    stats : PrimeProfileStats
    statsMatches :
      stats ≡ primeProfileStats arithmeticCarrier

    suite : PrimeProfileStatsSuite
    suiteMatches :
      suite ≡ primeProfileStatsSuite stats

    descriptiveCarrier : PrimeCarrier15
    descriptiveCarrierMatches :
      descriptiveCarrier ≡ primeProfileWeights stats

    descriptiveScore : Nat
    descriptiveScoreMatches :
      descriptiveScore ≡ primeProfileScore stats

    descriptiveRange : Nat
    descriptiveRangeMatches :
      descriptiveRange ≡ range15 descriptiveCarrier

    descriptiveNonZeroCount : Nat
    descriptiveNonZeroCountMatches :
      descriptiveNonZeroCount ≡ countNonZero15 descriptiveCarrier

    robustStats : PrimeProfileRobustStats stats
    inferenceStats : PrimeProfileInferenceStats stats

------------------------------------------------------------------------
-- Concrete packaging helper.

arithmeticPrimeProfileStatsBridge :
  PrimeCarrier15 →
  ArithmeticPrimeProfileStatsBridge
arithmeticPrimeProfileStatsBridge carrier = record
  { arithmeticCarrier = carrier
  ; stats = primeProfileStats carrier
  ; statsMatches = refl
  ; suite = primeProfileStatsSuite (primeProfileStats carrier)
  ; suiteMatches = refl
  ; descriptiveCarrier = primeProfileWeights (primeProfileStats carrier)
  ; descriptiveCarrierMatches = refl
  ; descriptiveScore = primeProfileScore (primeProfileStats carrier)
  ; descriptiveScoreMatches = refl
  ; descriptiveRange = range15 (primeProfileWeights (primeProfileStats carrier))
  ; descriptiveRangeMatches = refl
  ; descriptiveNonZeroCount = countNonZero15 (primeProfileWeights (primeProfileStats carrier))
  ; descriptiveNonZeroCountMatches = refl
  ; robustStats = primeProfileRobustStats (primeProfileStats carrier)
  ; inferenceStats = primeProfileInferenceStats (primeProfileStats carrier)
  }

------------------------------------------------------------------------
-- Narrow accessors for downstream consumers.

bridgeCarrier :
  ArithmeticPrimeProfileStatsBridge →
  PrimeCarrier15
bridgeCarrier = ArithmeticPrimeProfileStatsBridge.arithmeticCarrier

bridgeStats :
  ArithmeticPrimeProfileStatsBridge →
  PrimeProfileStats
bridgeStats = ArithmeticPrimeProfileStatsBridge.stats

bridgeSuite :
  ArithmeticPrimeProfileStatsBridge →
  PrimeProfileStatsSuite
bridgeSuite = ArithmeticPrimeProfileStatsBridge.suite

bridgeDescriptiveCarrier :
  ArithmeticPrimeProfileStatsBridge →
  PrimeCarrier15
bridgeDescriptiveCarrier = ArithmeticPrimeProfileStatsBridge.descriptiveCarrier

bridgeDescriptiveScore :
  ArithmeticPrimeProfileStatsBridge →
  Nat
bridgeDescriptiveScore = ArithmeticPrimeProfileStatsBridge.descriptiveScore

bridgeDescriptiveRange :
  ArithmeticPrimeProfileStatsBridge →
  Nat
bridgeDescriptiveRange = ArithmeticPrimeProfileStatsBridge.descriptiveRange

bridgeDescriptiveNonZeroCount :
  ArithmeticPrimeProfileStatsBridge →
  Nat
bridgeDescriptiveNonZeroCount =
  ArithmeticPrimeProfileStatsBridge.descriptiveNonZeroCount

bridgeRobustStats :
  (bridge : ArithmeticPrimeProfileStatsBridge) →
  PrimeProfileRobustStats (bridgeStats bridge)
bridgeRobustStats = ArithmeticPrimeProfileStatsBridge.robustStats

bridgeInferenceStats :
  (bridge : ArithmeticPrimeProfileStatsBridge) →
  PrimeProfileInferenceStats (bridgeStats bridge)
bridgeInferenceStats = ArithmeticPrimeProfileStatsBridge.inferenceStats
