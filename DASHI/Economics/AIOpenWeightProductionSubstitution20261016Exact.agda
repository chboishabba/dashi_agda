module DASHI.Economics.AIOpenWeightProductionSubstitution20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

platformTelemetryKind : Source.SourceKind
platformTelemetryKind = Source.namedSourceKind "platform-local production telemetry"

vercelOctoberIndex : Source.AttributedSource
vercelOctoberIndex = Source.mkNoDOISource
  "Vercel"
  "AI Gateway Production Index — October 2026"
  "production-traffic index"
  "2026-10-15"
  "https://vercel.com/blog/ai-gateway-production-index-october-2026"
  platformTelemetryKind
  "platform-local September 2026 telemetry: open-weight models 71.5 percent of gateway tokens and 23 percent of spend; total gateway spend about 13x December while average estimated price per token was 47 percent lower; model/lab switching increased"
  Source.publicAttribution

record GatewayProductionIndex : Set where
  constructor gateway-production-index
  field
    openWeightTokenSharePermille : Nat
    openWeightSpendSharePermille : Nat
    gatewaySpendVsDecemberTimes : Nat
    averagePricePerTokenDeclinePercent : Nat
    openWeightMajorityTokenVolumePaid : Bool
    spendGrowthPaid : Bool
    unitPriceCompressionPaid : Bool
    switchingPaid : Bool
    globalMarketSharePaid : Bool
    selfHostSharePaid : Bool
    sameCapabilitySubstitutionPaid : Bool
    frontierRevenueCollapsePaid : Bool

open GatewayProductionIndex public

septemberGatewayProductionIndex : GatewayProductionIndex
septemberGatewayProductionIndex = gateway-production-index
  715 230 13 47 true true true true false false false false

openWeightTokenShareIs715Permille :
  openWeightTokenSharePermille septemberGatewayProductionIndex ≡ 715
openWeightTokenShareIs715Permille = refl

openWeightSpendShareIs230Permille :
  openWeightSpendSharePermille septemberGatewayProductionIndex ≡ 230
openWeightSpendShareIs230Permille = refl

data GatewayImpliesGlobalSharePermission : Set where
data OpenWeightUsageImpliesSelfHostPermission : Set where
data TokenShareImpliesCapabilityParityPermission : Set where
data UnitPriceDeclineImpliesFrontierRevenueCollapsePermission : Set where

gatewayDoesNotCreateGlobalMarketShare : GatewayImpliesGlobalSharePermission → ⊥
gatewayDoesNotCreateGlobalMarketShare ()

openWeightUsageDoesNotCreateSelfHostShare : OpenWeightUsageImpliesSelfHostPermission → ⊥
openWeightUsageDoesNotCreateSelfHostShare ()

tokenShareDoesNotCreateCapabilityParity : TokenShareImpliesCapabilityParityPermission → ⊥
tokenShareDoesNotCreateCapabilityParity ()

unitPriceDeclineDoesNotCreateFrontierRevenueCollapse : UnitPriceDeclineImpliesFrontierRevenueCollapsePermission → ⊥
unitPriceDeclineDoesNotCreateFrontierRevenueCollapse ()

boundary : String
boundary =
  "Vercel's October 2026 production index supplies a strong platform-local substitution/compression observation: open-weight models processed 71.5 percent of September gateway tokens for 23 percent of estimated spend, while gateway spend was about 13x December and average estimated price per token 47 percent lower. This directly demonstrates volume growth, falling unit price and model/lab substitutability can coexist. The index is not global market share, does not distinguish hosted open-weight from self-hosting, does not prove same-capability parity, and does not establish frontier-lab revenue collapse."
