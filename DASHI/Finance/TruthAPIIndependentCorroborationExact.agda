module DASHI.Finance.TruthAPIIndependentCorroborationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradePrimarySourceRound3Exact as Round3

------------------------------------------------------------------------
-- INDEPENDENT CORROBORATION OF TRUTH API LAUNCH / CUSTOMER-COUNT CLAIMS
--
-- Reuters independently reported the August 1 launch, revenue generation and
-- more-than-ten customer agreements after TMTG's SEC-filed Q2 disclosures.
-- This pays an independent-corroboration axis for those narrow propositions.
-- It does not convert Reuters into primary contract evidence or identify the
-- customers, contract terms, measured latency advantage, legal status, motive
-- or trading outcomes.
------------------------------------------------------------------------

truthAPIReutersCorroboration : Atlas.TradeEvidenceClaim
truthAPIReutersCorroboration =
  Atlas.tradeEvidenceClaim
    "Reuters-Truth-API-Q2-2026-08-11"
    "Trump Media & Technology Group Corp."
    "Truth API launch / signed-customer / revenue claims"
    Atlas.marketDataProductClaim
    "2026-08-01 launch; status reported 2026-08-11"
    "2026-08-11"
    "Reuters independently reported that Truth API had launched on August 1, had signed more than ten customer agreements, and had begun generating revenue, citing Trump Media's second-quarter disclosure."
    Atlas.independentSynthesisSupport
    (Atlas.sourceCitation
      "Reuters"
      "Trump Media's quarterly loss widens to $238 million from $20 million a year earlier"
      "2026-08-11"
      "no DOI"
      "https://www.reuters.com/world/us/trump-medias-quarterly-loss-widens-238-million-20-million-year-earlier-2026-08-11/"
      Atlas.independentReporting)
    (DASHI.Core.SourceConditionedObservationExact.sourceArtifact
      "Reuters-2026-08-11-TMTG-Q2-Truth-API"
      DASHI.Core.SourceConditionedObservationExact.derivedArtifact
      "https://www.reuters.com/world/us/trump-medias-quarterly-loss-widens-238-million-20-million-year-earlier-2026-08-11/"
      "Reuters")
    "Corroborates launch, more-than-ten signed agreements, and revenue generation at the level reported by Reuters. It does not pay individual customer identity or contract terms."
    false true false false

record CorroborationPair : Set₁ where
  constructor corroboration-pair
  field
    primaryClaim : Atlas.TradeEvidenceClaim
    independentClaim : Atlas.TradeEvidenceClaim
    sameNarrowProposition : Set
    sameNarrowPropositionReceipt : sameNarrowProposition
    primaryIsPaid : Atlas.primarySourcePaid primaryClaim ≡ true
    independentIsPaid : Atlas.independentCorroborationPaid independentClaim ≡ true

open CorroborationPair public

data TruthAPILaunchCustomerRevenueProposition : Set where
  truthAPILaunchCustomerRevenueProposition : TruthAPILaunchCustomerRevenueProposition

truthAPILaunchCorroboration : CorroborationPair
truthAPILaunchCorroboration =
  corroboration-pair
    Round3.truthAPIRealisedLaunchAndCustomers
    truthAPIReutersCorroboration
    TruthAPILaunchCustomerRevenueProposition
    truthAPILaunchCustomerRevenueProposition
    refl
    refl

------------------------------------------------------------------------
-- Corroboration boundaries.
------------------------------------------------------------------------

data IndependentReportingAutomaticallyPaysContractIdentity : Set where
data TwoSourcesAutomaticallyProveLegalStatus : Set where
data RevenueReportAutomaticallyProvesProfitableCustomerTrading : Set where

corroborationDoesNotPayContractIdentity :
  IndependentReportingAutomaticallyPaysContractIdentity → ⊥
corroborationDoesNotPayContractIdentity ()

twoSourcesDoNotProveLegalStatus :
  TwoSourcesAutomaticallyProveLegalStatus → ⊥
twoSourcesDoNotProveLegalStatus ()

revenueDoesNotProveCustomerTradingProfit :
  RevenueReportAutomaticallyProvesProfitableCustomerTrading → ⊥
revenueDoesNotProveCustomerTradingProfit ()

record TruthAPIIndependentCorroborationBoundary : Set where
  constructor truth-api-independent-corroboration-boundary
  field
    primaryAndIndependentSourcesAreDistinct : Bool
    launchNowHasIndependentCorroboration : Bool
    customerCountNowHasIndependentCorroboration : Bool
    revenueGenerationNowHasIndependentCorroboration : Bool
    customerIdentityStillUnpaid : Bool
    contractTermsStillUnpaid : Bool
    legalStatusStillUnpaid : Bool
    customerTradingOutcomeStillUnpaid : Bool

canonicalTruthAPIIndependentCorroborationBoundary :
  TruthAPIIndependentCorroborationBoundary
canonicalTruthAPIIndependentCorroborationBoundary =
  truth-api-independent-corroboration-boundary
    true true true true true true true true
