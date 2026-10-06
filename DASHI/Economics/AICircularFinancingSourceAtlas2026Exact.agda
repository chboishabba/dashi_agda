module DASHI.Economics.AICircularFinancingSourceAtlas2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital

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

------------------------------------------------------------------------
-- Attribution firewall.
------------------------------------------------------------------------

data SecondaryGraphImpliesPrimaryTransactionTermsPermission : Set where
data PlatformTelemetryImpliesGlobalMarketSharePermission : Set where

data UnsourcedAcquisitionImpliesAcquisitionFactPermission : Set where

secondaryGraphDoesNotAutoProvePrimaryTransactionTerms :
  SecondaryGraphImpliesPrimaryTransactionTermsPermission → ⊥
secondaryGraphDoesNotAutoProvePrimaryTransactionTerms ()

platformTelemetryDoesNotAutoProveGlobalMarketShare :
  PlatformTelemetryImpliesGlobalMarketSharePermission → ⊥
platformTelemetryDoesNotAutoProveGlobalMarketShare ()

unsourcedAcquisitionDoesNotAutoPromoteToFact :
  UnsourcedAcquisitionImpliesAcquisitionFactPermission → ⊥
unsourcedAcquisitionDoesNotAutoPromoteToFact ()
