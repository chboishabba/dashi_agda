module DASHI.Finance.TrumpFamilyExternalCounterpartyPrimaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyExternalCounterpartyEvidenceExact as Counterparty

------------------------------------------------------------------------
-- PRIMARY COUNTERPARTY PAYMENT
--
-- MGX's own March 12, 2025 announcement pays the existence, size, minority-
-- stake and stablecoin-payment propositions for the Binance investment.  It
-- does NOT identify USD1 in that announcement.  The separate Reuters/WLFI edge
-- remains necessary for the later USD1-selection proposition.
------------------------------------------------------------------------

mgxBinancePrimaryInvestment : Counterparty.CounterpartyEvidence
mgxBinancePrimaryInvestment =
  Counterparty.counterpartyEvidence
    "MGX (Abu Dhabi)"
    "Binance"
    Counterparty.stablecoinSettlementRelation
    "2025-03-12 announcement"
    "MGX and Binance announced a $2 billion minority investment by MGX in Binance, described by MGX as the first institutional investment in Binance and the largest investment paid in crypto/stablecoin. The MGX announcement does not identify the stablecoin as USD1."
    (Atlas.sourceCitation
      "MGX; Binance"
      "MGX Backs Binance in Landmark Investment"
      "2025-03-12"
      "no DOI"
      "https://www.mgx.ae/news-insights/mgx-backs-binance-landmark-investment"
      Atlas.companyProductDisclosure)
    (Source.sourceArtifact
      "MGX-2025-03-12-Binance-investment"
      Source.documentaryArtifact
      "https://www.mgx.ae/news-insights/mgx-backs-binance-landmark-investment"
      "MGX")
    true false false false

record CrossSourceSettlementIdentity : Set₁ where
  constructor cross-source-settlement-identity
  field
    primaryTransaction : Counterparty.CounterpartyEvidence
    independentUSD1Identification : Counterparty.CounterpartyEvidence
    sameTransactionReference : String
    primaryNamesUSD1 : Bool
    primaryNamesUSD1IsFalse : primaryNamesUSD1 ≡ false
    independentSourceNamesUSD1 : Bool
    independentSourceNamesUSD1IsTrue : independentSourceNamesUSD1 ≡ true

open CrossSourceSettlementIdentity public

mgxSettlementCrossSource : CrossSourceSettlementIdentity
mgxSettlementCrossSource =
  cross-source-settlement-identity
    mgxBinancePrimaryInvestment
    Counterparty.mgxBinanceUSD1Settlement
    "MGX March 12 primary announcement pays the $2bn Binance minority-investment/stablecoin event; Reuters May 1 reporting pays the later attribution that WLFI co-founder Zach Witkoff identified USD1 as the settlement rail"
    false refl
    true refl

------------------------------------------------------------------------
-- The cross-source composition may strengthen transaction identity without
-- manufacturing policy causation, personal receipt or quid-pro-quo claims.
------------------------------------------------------------------------

data StablecoinIdentityAutomaticallyMeansPolicyInfluence : Set where
data TransactionScaleAutomaticallyMeansPersonalGain : Set where

stablecoinIdentityDoesNotProvePolicyInfluence :
  StablecoinIdentityAutomaticallyMeansPolicyInfluence → ⊥
stablecoinIdentityDoesNotProvePolicyInfluence ()

transactionScaleDoesNotEqualPersonalGain :
  TransactionScaleAutomaticallyMeansPersonalGain → ⊥
transactionScaleDoesNotEqualPersonalGain ()

record TrumpFamilyExternalCounterpartyPrimaryBoundary : Set where
  constructor trump-family-external-counterparty-primary-boundary
  field
    primaryTransactionExistencePaid : Bool
    primaryStablecoinPaymentPaid : Bool
    primaryUSD1IdentityUnpaid : Bool
    independentUSD1IdentityPaid : Bool
    crossSourceCompositionDoesNotCreatePolicyCausation : Bool

canonicalTrumpFamilyExternalCounterpartyPrimaryBoundary :
  TrumpFamilyExternalCounterpartyPrimaryBoundary
canonicalTrumpFamilyExternalCounterpartyPrimaryBoundary =
  trump-family-external-counterparty-primary-boundary true true true true true
