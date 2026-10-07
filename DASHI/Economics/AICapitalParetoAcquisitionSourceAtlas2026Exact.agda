module DASHI.Economics.AICapitalParetoAcquisitionSourceAtlas2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SOURCE ATLAS FOR THE RESIDUAL-CONDITIONED ACQUISITION FRONTIER
--
-- These sources may improve acquisition routes.  Their presence does not
-- close a producer, prove causality, create a scalar Pareto winner, or supply
-- terminal capital-recovery authority.
------------------------------------------------------------------------

anthropicProfitabilityReuters20261007 : Source.AttributedSource
anthropicProfitabilityReuters20261007 = Source.mkNoDOISource
  "Reuters Open Interest"
  "Can AI labs ever turn a profit?"
  "Reuters"
  "2026-10-07"
  "https://www.reuters.com/commentary/reuters-open-interest/can-ai-labs-ever-turn-profit-joachim-klement-2026-10-07/"
  Source.newsSource
  "secondary carrier for Anthropic 2025 revenue USD 4.6B, operating loss USD 8.06B and compute/infrastructure spend USD 7.3B; supports a negative operating-return diagnostic but not realised ROIC-WACC"
  Source.publicAttribution

aiCreditReuters20260922 : Source.AttributedSource
aiCreditReuters20260922 = Source.mkNoDOISource
  "Reuters"
  "Corporate bond buyers get picky with flood of AI debt"
  "Reuters"
  "2026-09-22"
  "https://www.reuters.com/legal/transactional/corporate-bond-buyers-get-picky-with-flood-ai-debt-2026-09-22/"
  Source.newsSource
  "secondary carrier for AI-related investment-grade spreads around 115 bp versus 78 bp for broad investment grade; closes a funding-stress observation, not WACC or rollover"
  Source.publicAttribution

gpuCollateralReuters20261001 : Source.AttributedSource
gpuCollateralReuters20261001 = Source.mkNoDOISource
  "Reuters"
  "Nvidia's bet that its chips can finance the AI boom gets a Wall Street reality check"
  "Reuters"
  "2026-10-01"
  "https://www.reuters.com/legal/transactional/nvidias-bet-that-its-chips-can-finance-ai-boom-gets-wall-street-reality-check-2026-10-01/"
  Source.newsSource
  "secondary carrier for lender practice using roughly 3-4 year GPU depreciation assumptions and demands for revenue/customer support; informs replacement/obsolescence acquisition only"
  Source.publicAttribution

aiBorrowersReuters20260930 : Source.AttributedSource
aiBorrowersReuters20260930 = Source.mkNoDOISource
  "Reuters"
  "AI borrowers face tough sell in risky corners of US credit market"
  "Reuters"
  "2026-09-30"
  "https://www.reuters.com/legal/transactional/ai-borrowers-face-tough-sell-risky-corners-us-credit-market-2026-09-30/"
  Source.newsSource
  "secondary carrier for AI leveraged-finance growth and high-single-digit/near-10-percent reported yields; funding stress is not the same object as borrower-specific rollover dependence"
  Source.publicAttribution

fercPJMReuters20260930 : Source.AttributedSource
fercPJMReuters20260930 = Source.mkNoDOISource
  "Reuters"
  "FERC asks grid operator PJM to revise plan to shield homes from data center costs"
  "Reuters"
  "2026-09-30"
  "https://www.reuters.com/business/energy/ferc-asks-grid-operator-pjm-revise-plan-shield-homes-data-center-costs-2026-09-30/"
  Source.newsSource
  "secondary carrier for FERC/PJM data-centre backstop procurement and cost-allocation intervention; policy salience is not a numeric backstop probability or capture finding"
  Source.publicAttribution

aragonDataCentreReuters20261006 : Source.AttributedSource
aragonDataCentreReuters20261006 = Source.mkNoDOISource
  "Reuters"
  "Fast-track permits turn Spain's Aragon into a $70 billion data centre magnet. At what cost?"
  "Reuters"
  "2026-10-06"
  "https://www.reuters.com/technology/fast-track-permits-turn-spains-aragon-into-70-billion-data-centre-magnet-what-2026-10-06/"
  Source.newsSource
  "secondary carrier for geographically local fast-track permitting associated with large data-centre investment; local facilitation is not a global AI policy-backstop score"
  Source.publicAttribution

aiCapitalParetoAcquisitionAtlas : Source.AttributedSourceAtlas
aiCapitalParetoAcquisitionAtlas = Source.mkSourceAtlas
  "AI capital Pareto acquisition source atlas, October 2026"
  "DASHI.Economics.AICapitalParetoAcquisitionSourceAtlas2026Exact"
  (anthropicProfitabilityReuters20261007 ∷
   aiCreditReuters20260922 ∷
   gpuCollateralReuters20261001 ∷
   aiBorrowersReuters20260930 ∷
   fercPJMReuters20260930 ∷
   aragonDataCentreReuters20261006 ∷ [])
  "source-bounded acquisition evidence for profitability direction, funding stress, replacement/obsolescence, refinancing/funding and policy-support residual routes; sources do not themselves close the runtime producer vector except where a separately declared point observation is explicitly constructed"

atlasDoesNotCreateAuthority :
  Source.atlasCreatesAuthority aiCapitalParetoAcquisitionAtlas ≡ false
atlasDoesNotCreateAuthority = refl
