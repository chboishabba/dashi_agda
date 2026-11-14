module DASHI.Economics.AIOpenWeightMarketTransition2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital

------------------------------------------------------------------------
-- OPEN-WEIGHT PRODUCTION-USAGE TRANSITION, 2026
--
-- Platform telemetry is evidence about the platform, not a global market-share
-- census.  Token share and spend share are kept separate because their
-- divergence is itself economically informative.
------------------------------------------------------------------------

platformTelemetryKind : Source.SourceKind
platformTelemetryKind = Source.namedSourceKind "primary platform telemetry"

vercelSeptember2026 : Source.AttributedSource
vercelSeptember2026 = Source.mkNoDOISource
  "Vercel"
  "Open-weight models take 56% of token volume, Astra doubles Fable 5.1 spend"
  "AI Gateway Production Index — September 2026"
  "2026-09-17"
  "https://vercel.com/blog/ai-gateway-production-index-september-2026"
  platformTelemetryKind
  "primary platform telemetry: open-weight token share rose from 7% in December 2025 to 56% in August 2026, while August open-weight spend share was 14%; average token price fell 23.2% in August"
  Source.publicAttribution

vercelAugust2026 : Source.AttributedSource
vercelAugust2026 = Source.mkNoDOISource
  "Vercel"
  "DeepSeek overtakes Google on volume, cost per token falls 13.6%"
  "AI Gateway Production Index — August 2026"
  "2026-08-11"
  "https://vercel.com/blog/deepseek-overtakes-google-on-volume-cost-per-token-falls"
  platformTelemetryKind
  "primary platform telemetry: Anthropic received 65% of gateway spend on 30% of token volume in July 2026, preserving evidence of a premium frontier-spend tier despite open-weight volume growth"
  Source.publicAttribution

record PlatformTransition : Set where
  constructor platformTransition
  field
    platform : String
    startWindow : String
    endWindow : String
    startOpenTokenShare : String
    endOpenTokenShare : String
    endOpenSpendShare : String
    source : Source.AttributedSource
    openMajorityReached : Bool
    globalMarketMajorityEstablished : Bool

open PlatformTransition public

vercelOpenWeightTransition : PlatformTransition
vercelOpenWeightTransition = platformTransition
  "Vercel AI Gateway"
  "December 2025"
  "August 2026"
  "7 percent"
  "56 percent"
  "14 percent"
  vercelSeptember2026
  true
  false

record PremiumFrontierResidual : Set where
  constructor premiumFrontierResidual
  field
    provider : String
    window : String
    tokenShareReading : String
    spendShareReading : String
    premiumSpendResidualObserved : Bool
    provesDurableMoat : Bool

open PremiumFrontierResidual public

anthropicPremiumResidualJuly2026 : PremiumFrontierResidual
anthropicPremiumResidualJuly2026 = premiumFrontierResidual
  "Anthropic on Vercel AI Gateway"
  "July 2026"
  "30 percent token volume"
  "65 percent spend"
  true
  false

record OpenWeightFlipBoundary : Set where
  constructor openWeightFlipBoundary
  field
    kiloNearEightyPercentOpen : Bool
    vercelOpenMajority : Bool
    productionUsageShiftStrong : Bool
    exactGlobalEightyTwentyFlipEstablished : Bool

open OpenWeightFlipBoundary public

sourceBoundedOpenWeightFlip : OpenWeightFlipBoundary
sourceBoundedOpenWeightFlip =
  openWeightFlipBoundary true true true false

data PlatformMajorityImpliesGlobalMajorityPermission : Set where
data SpendPremiumImpliesDurableMoatPermission : Set where
data TokenShareImpliesProfitSharePermission : Set where

platformMajorityDoesNotAutoProveGlobalMajority :
  PlatformMajorityImpliesGlobalMajorityPermission → ⊥
platformMajorityDoesNotAutoProveGlobalMajority ()

spendPremiumDoesNotAutoProveDurableMoat :
  SpendPremiumImpliesDurableMoatPermission → ⊥
spendPremiumDoesNotAutoProveDurableMoat ()

tokenShareDoesNotAutoProveProfitShare :
  TokenShareImpliesProfitSharePermission → ⊥
tokenShareDoesNotAutoProveProfitShare ()

kiloCurrentUsageReceipt : Capital.BoundedObservation
kiloCurrentUsageReceipt = Capital.kiloOpenWeightUsageObservation
