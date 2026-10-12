module DASHI.Economics.AIEqualIndexOpenClosedSpread20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- EQUAL-AGGREGATE-INDEX OPEN/CLOSED SPREAD
--
-- Artificial Analysis currently reports MiMo-V2.6-Pro (open weights) and
-- GPT-6 Astra (Low) (closed) at the SAME Intelligence Index score: 46.
-- This pays a substantially stronger matched scalar comparison than the older
-- MiMo-vs-Opus pair.  It does NOT prove that the two capability vectors are
-- identical: their benchmark components differ materially.
------------------------------------------------------------------------

benchmarkKind : Source.SourceKind
benchmarkKind = Source.namedSourceKind "third-party benchmark and price comparison"

artificialAnalysisEqualIndexSource : Source.AttributedSource
artificialAnalysisEqualIndexSource = Source.mkNoDOISource
  "Artificial Analysis"
  "MiMo-V2.6-Pro vs GPT-6 Astra (Low)"
  "model comparison / Intelligence Index v4.3.2"
  "2026-10-12"
  "https://artificialanalysis.ai/models/comparisons/mimo-v2-6-pro-vs-gpt-6-astra-low"
  benchmarkKind
  "same benchmark page reports Intelligence Index 46 for both models; MiMo open weights / MIT, Astra closed; weighted cost per task USD 0.13 vs USD 0.82; blended price per 1M tokens USD 0.1765 vs USD 7.70; component benchmark scores differ"
  Source.publicAttribution

record EqualIndexPair : Set where
  constructor equal-index-pair
  field
    openModel : String
    closedModel : String
    openWeights : Bool
    closedWeights : Bool
    openIndex : Nat
    closedIndex : Nat
    openCostPerTaskCents : Nat
    closedCostPerTaskCents : Nat
    openBlendedPriceTenThousandthsUSD : Nat
    closedBlendedPriceTenThousandthsUSD : Nat
    openTerminalBenchPercent : Nat
    closedTerminalBenchPercent : Nat
    openSciCodePercent : Nat
    closedSciCodePercent : Nat
    openOmniscience : Nat
    closedOmniscience : Nat
    sameAggregateIndexPaid : Bool
    sameCapabilityVectorPaid : Bool
    sameContextWindowPaid : Bool
    similarOutputSpeedObserved : Bool
    source : Source.AttributedSource

open EqualIndexPair public

mimoAstraEqualIndexPair : EqualIndexPair
mimoAstraEqualIndexPair = equal-index-pair
  "MiMo-V2.6-Pro"
  "GPT-6 Astra (Low)"
  true false
  46 46
  13 82
  1765 77000
  35 42
  61 54
  8 41
  true false true true
  artificialAnalysisEqualIndexSource

bothIntelligenceIndex46 :
  openIndex mimoAstraEqualIndexPair ≡ 46
  × closedIndex mimoAstraEqualIndexPair ≡ 46
bothIntelligenceIndex46 = refl , refl

sameAggregateIndexPaidReceipt :
  sameAggregateIndexPaid mimoAstraEqualIndexPair ≡ true
sameAggregateIndexPaidReceipt = refl

sameCapabilityVectorPaidIsFalse :
  sameCapabilityVectorPaid mimoAstraEqualIndexPair ≡ false
sameCapabilityVectorPaidIsFalse = refl

------------------------------------------------------------------------
-- Exact ratio lower-bound receipts without division.
--
-- Cost/task: 13 cents * 6 = 78 cents, 4 cents below 82 cents.
-- Blended token price: 0.1765 * 43 = 7.5895, 0.1105 below 7.70.
------------------------------------------------------------------------

costPerTaskClosedOpenRatioAbove6xWitness :
  13 * 6 + 4 ≡ 82
costPerTaskClosedOpenRatioAbove6xWitness = refl

costPerTaskClosedOpenRatioAbove6x : Bool
costPerTaskClosedOpenRatioAbove6x = true

blendedTokenPriceClosedOpenRatioAbove43xWitness :
  1765 * 43 + 1105 ≡ 77000
blendedTokenPriceClosedOpenRatioAbove43xWitness = refl

blendedTokenPriceClosedOpenRatioAbove43x : Bool
blendedTokenPriceClosedOpenRatioAbove43x = true

------------------------------------------------------------------------
-- Scalar collision: the aggregate score is equal while multiple coordinates
-- differ.  This directly blocks promotion from "same scalar index" to
-- "same capability vector".
------------------------------------------------------------------------

terminalBenchComponentsDiffer :
  openTerminalBenchPercent mimoAstraEqualIndexPair ≡
  closedTerminalBenchPercent mimoAstraEqualIndexPair → ⊥
terminalBenchComponentsDiffer ()

sciCodeComponentsDiffer :
  openSciCodePercent mimoAstraEqualIndexPair ≡
  closedSciCodePercent mimoAstraEqualIndexPair → ⊥
sciCodeComponentsDiffer ()

omniscienceComponentsDiffer :
  openOmniscience mimoAstraEqualIndexPair ≡
  closedOmniscience mimoAstraEqualIndexPair → ⊥
omniscienceComponentsDiffer ()

data EqualScalarIndexImpliesCapabilityIdentityPermission : Set where
data EqualIndexPriceGapImpliesGlobalScarcityRentPermission : Set where

equalScalarIndexDoesNotCreateCapabilityIdentity :
  EqualScalarIndexImpliesCapabilityIdentityPermission → ⊥
equalScalarIndexDoesNotCreateCapabilityIdentity ()

equalIndexPriceGapDoesNotCreateGlobalScarcityRent :
  EqualIndexPriceGapImpliesGlobalScarcityRentPermission → ⊥
equalIndexPriceGapDoesNotCreateGlobalScarcityRent ()

boundary : String
boundary =
  "Artificial Analysis v4.3.2 reports MiMo-V2.6-Pro (open weights) and GPT-6 Astra Low (closed) at exactly the same aggregate Intelligence Index score, 46. On the same page the closed model costs USD 0.82 versus USD 0.13 per weighted index task (>6x) and USD 7.70 versus USD 0.1765 per 1M blended tokens (>43x). This closes an equal-aggregate-index price/cost spread. It does not establish full capability identity: Terminal-Bench, SciCode, Omniscience and other component coordinates differ, so the equal scalar score cannot be promoted into a global same-capability scarcity-rent theorem."
