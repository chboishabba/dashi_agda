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
  (gpuCollateralReuters20261001 ∷
   aiBorrowersReuters20260930 ∷
   fercPJMReuters20260930 ∷
   aragonDataCentreReuters20261006 ∷ [])
  "source-bounded acquisition evidence for replacement/obsolescence, refinancing/funding and policy-support residual routes; sources do not themselves close the runtime producer vector"

atlasDoesNotCreateAuthority :
  Source.atlasCreatesAuthority aiCapitalParetoAcquisitionAtlas ≡ false
atlasDoesNotCreateAuthority = refl
