module DASHI.Economics.AIQualityNormalizedPriceSpread20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SELECTED BENCHMARK-NORMALISED API PRICE PAIR
--
-- The common denominator is the Artificial Analysis Intelligence Index family,
-- not equal capability. API price is also not provider marginal serving cost.
------------------------------------------------------------------------

benchmarkSourceKind : Source.SourceKind
benchmarkSourceKind = Source.namedSourceKind "independent model benchmark and API-price analysis"

mimoSource : Source.AttributedSource
mimoSource = Source.mkNoDOISource
  "Artificial Analysis"
  "MiMo-V2.6-Pro - Intelligence, Performance & Price Analysis"
  "Artificial Analysis"
  "2026-09"
  "https://artificialanalysis.ai/models/mimo-v2-6-pro/"
  benchmarkSourceKind
  "carrier for open-weight MiMo-V2.6-Pro Intelligence Index 46 and USD 0.13 cost per Intelligence Index task"
  Source.publicAttribution

opusSource : Source.AttributedSource
opusSource = Source.mkNoDOISource
  "Artificial Analysis"
  "Claude Opus 5.5: Release Intelligence, Performance & Price"
  "Artificial Analysis"
  "2026-09"
  "https://artificialanalysis.ai/models/releases/claude-opus-5-5"
  benchmarkSourceKind
  "carrier for proprietary Claude Opus 5.5 Max Intelligence Index 58 and USD 5.98 cost per Intelligence Index task"
  Source.publicAttribution

record BenchmarkPricePoint : Set where
  constructor benchmarkPricePoint
  field
    model : String
    openWeights : Bool
    intelligenceIndex : Nat
    costPerTaskCents : Nat
    source : Source.AttributedSource

open BenchmarkPricePoint public

mimoPricePoint : BenchmarkPricePoint
mimoPricePoint = benchmarkPricePoint "MiMo-V2.6-Pro" true 46 13 mimoSource

opusPricePoint : BenchmarkPricePoint
opusPricePoint = benchmarkPricePoint "Claude Opus 5.5 Max" false 58 598 opusSource

record BenchmarkNormalisedPricePair : Set where
  constructor benchmarkNormalisedPricePair
  field
    openPoint : BenchmarkPricePoint
    closedPoint : BenchmarkPricePoint
    closedToOpenCostPerIndexPointRatioMilli : Nat
    selectedPairClosed : Bool
    sameCapabilityEquivalenceClosed : Bool
    providerMarginClosed : Bool
    globalScarcityRentClosed : Bool

open BenchmarkNormalisedPricePair public

mimoVsOpusBenchmarkPricePair : BenchmarkNormalisedPricePair
mimoVsOpusBenchmarkPricePair = benchmarkNormalisedPricePair
  mimoPricePoint opusPricePoint
  36483 true false false false

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data BenchmarkNormalisationImpliesEqualCapabilityPermission : Set where
data APIPriceImpliesServingMarginPermission : Set where
data SelectedPairImpliesGlobalScarcityRentPermission : Set where

benchmarkNormalisationDoesNotAutoProveEqualCapability :
  BenchmarkNormalisationImpliesEqualCapabilityPermission → ⊥
benchmarkNormalisationDoesNotAutoProveEqualCapability ()

apiPriceDoesNotAutoCreateServingMargin : APIPriceImpliesServingMarginPermission → ⊥
apiPriceDoesNotAutoCreateServingMargin ()

selectedPairDoesNotAutoCreateGlobalScarcityRent :
  SelectedPairImpliesGlobalScarcityRentPermission → ⊥
selectedPairDoesNotAutoCreateGlobalScarcityRent ()

selectedPairIsPaid : selectedPairClosed mimoVsOpusBenchmarkPricePair ≡ true
selectedPairIsPaid = refl

sameCapabilityStillOpen : sameCapabilityEquivalenceClosed mimoVsOpusBenchmarkPricePair ≡ false
sameCapabilityStillOpen = refl

providerMarginStillOpen : providerMarginClosed mimoVsOpusBenchmarkPricePair ≡ false
providerMarginStillOpen = refl

globalScarcityRentStillOpen : globalScarcityRentClosed mimoVsOpusBenchmarkPricePair ≡ false
globalScarcityRentStillOpen = refl
