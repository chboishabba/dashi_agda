module DASHI.Economics.AIOpenWeightProviderIntermediation20261016Exact where

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
  "Vercel reports that 68 percent of teams increasing open-weight spend also increased closed-weight spend; nearly 70 percent of September spend on Chinese-origin models flowed through US-based providers; frontier-model spend rose roughly tenfold since December while open-weight spend rose more than seventyfold."
  Source.publicAttribution

record ProviderIntermediationState : Set where
  constructor provider-intermediation-state
  field
    teamsIncreasingBothOpenAndClosedPercent : Nat
    chineseModelSpendViaUSProvidersPercentLowerBound : Nat
    frontierSpendGrowthVsDecemberTimesLowerBound : Nat
    openWeightSpendGrowthVsDecemberTimesLowerBound : Nat
    bothOpenAndClosedSpendGrowthPaid : Bool
    usProviderChineseModelIntermediationPaid : Bool
    openWeightImpliesDisintermediation : Bool
    openWeightImpliesFrontierRevenueCollapse : Bool
    globalProviderRentTransferEstablished : Bool

open ProviderIntermediationState public

vercelProviderIntermediation : ProviderIntermediationState
vercelProviderIntermediation = provider-intermediation-state
  68 69 10 70 true true false false false

bothSidesGrowthPaid : bothOpenAndClosedSpendGrowthPaid vercelProviderIntermediation ≡ true
bothSidesGrowthPaid = refl

usProviderIntermediationPaid : usProviderChineseModelIntermediationPaid vercelProviderIntermediation ≡ true
usProviderIntermediationPaid = refl

data OpenWeightImpliesProviderDisintermediationPermission : Set where
data IntermediationImpliesGlobalRentTransferPermission : Set where

openWeightDoesNotForceProviderDisintermediation : OpenWeightImpliesProviderDisintermediationPermission → ⊥
openWeightDoesNotForceProviderDisintermediation ()

platformIntermediationDoesNotEstablishGlobalRentTransfer : IntermediationImpliesGlobalRentTransferPermission → ⊥
platformIntermediationDoesNotEstablishGlobalRentTransfer ()

boundary : String
boundary =
  "Vercel's September production telemetry shows open-weight growth does not imply provider or frontier disintermediation on this platform. Most teams that increased open-weight spending also increased closed-weight spending, and a large majority of spend on Chinese-origin models was intermediated by US-based providers. Frontier spend also grew strongly while open-weight spend grew much faster. This is evidence compatible with capital/value rotation from model scarcity toward hosting, routing and application layers. It is platform-local telemetry, not global market share, not audited provider profit, not proof of a permanent rent transfer, and not evidence that open weights cease competing with closed models."
