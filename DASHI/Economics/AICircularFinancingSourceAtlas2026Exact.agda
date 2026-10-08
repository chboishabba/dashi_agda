module DASHI.Economics.AICircularFinancingSourceAtlas2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital
import DASHI.Economics.AnthropicProspectusCapitalRecovery2026Exact as Anthropic
import DASHI.Economics.AISlimMoECostCompression2026Exact as SlimMoE
import DASHI.Economics.AIOpenWeightMarketTransition2026Exact as OpenTransition

------------------------------------------------------------------------
-- SOURCE ATLAS FOR THE OCTOBER 2026 CIRCULAR-FINANCING TRANCHE
--
-- Primary sources are preferred for transaction terms and company-reported
-- metrics.  Reuters is used for independently reported market/funding context.
-- Platform telemetry is explicitly scoped to the reporting platform.
------------------------------------------------------------------------

record AtlasEntry : Set where
  constructor atlasEntry
  field
    proposition : String
    source : Source.AttributedSource
    primaryCarrierPreferred : Bool
    globalGeneralisationAllowed : Bool

open AtlasEntry public

cerebrasPartnershipEntry : AtlasEntry
cerebrasPartnershipEntry = atlasEntry
  "OpenAI and Cerebras announced a 750 MW low-latency inference partnership; no acquisition proposition is carried by the cited primary source."
  Capital.cerebrasOpenAIPartnershipSource true false

softbankFundingEntry : AtlasEntry
softbankFundingEntry = atlasEntry
  "SoftBank AI-linked borrowing was reported at high-single-digit to near-10% yields, supporting a funding-stress coordinate rather than a universal hurdle-rate law."
  Capital.softbankCreditReuters2026 false false

kiloUsageEntry : AtlasEntry
kiloUsageEntry = atlasEntry
  "Kilo reported 79.1% open-weight token usage for the cited July 2026 week; the observation is platform-local."
  Capital.kiloOpenWeightShare2026 true false

vercelUsageSpendEntry : AtlasEntry
vercelUsageSpendEntry = atlasEntry
  "Vercel reported open-weight token volume far above its spend share in June 2026, supporting a usage/rent divergence observation on that gateway."
  Capital.vercelOpenWeightShare2026 true false

vercelTransitionEntry : AtlasEntry
vercelTransitionEntry = atlasEntry
  "Vercel reported open-weight token share rising from 7% in December 2025 to 56% in August 2026, with 14% of August spend; this is gateway-local telemetry."
  OpenTransition.vercelSeptember2026 true false

slimMoEEntry : AtlasEntry
slimMoEEntry = atlasEntry
  "SlimMoE compresses Phi-3.5-MoE 41.9B/6.6B-active into 7.6B/2.4B-active and 3.8B/1.1B-active variants using 400B distillation tokens, with source-reported single-GPU fine-tuning feasibility."
  SlimMoE.slimMoEPaper true false

anthropicOperatingLossEntry : AtlasEntry
anthropicOperatingLossEntry = atlasEntry
  "Anthropic's prospectus reporting distinguishes more than USD 8 billion of operating loss from the much larger GAAP net loss affected by financing-instrument accounting."
  Anthropic.reutersS1QA2026 false false

anthropicBroadcomEntry : AtlasEntry
anthropicBroadcomEntry = atlasEntry
  "Broadcom-linked financing of up to USD 42 billion is associated with Anthropic's five-year USD 125.2 billion compute-capacity commitment and includes a convertible instrument."
  Anthropic.reutersBroadcomLoan2026 false false

------------------------------------------------------------------------
-- Attribution firewall.
------------------------------------------------------------------------

data SecondaryGraphImpliesPrimaryTransactionTermsPermission : Set where
data PlatformTelemetryImpliesGlobalMarketSharePermission : Set where
data UnsourcedAcquisitionImpliesAcquisitionFactPermission : Set where
data SourceCitationImpliesCausalEconomicTheoremPermission : Set where

secondaryGraphDoesNotAutoProvePrimaryTransactionTerms :
  SecondaryGraphImpliesPrimaryTransactionTermsPermission → ⊥
secondaryGraphDoesNotAutoProvePrimaryTransactionTerms ()

platformTelemetryDoesNotAutoProveGlobalMarketShare :
  PlatformTelemetryImpliesGlobalMarketSharePermission → ⊥
platformTelemetryDoesNotAutoProveGlobalMarketShare ()

unsourcedAcquisitionDoesNotAutoPromoteToFact :
  UnsourcedAcquisitionImpliesAcquisitionFactPermission → ⊥
unsourcedAcquisitionDoesNotAutoPromoteToFact ()

sourceCitationDoesNotAutoProveCausalEconomicTheorem :
  SourceCitationImpliesCausalEconomicTheoremPermission → ⊥
sourceCitationDoesNotAutoProveCausalEconomicTheorem ()
