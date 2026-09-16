module DASHI.Finance.TrumpFamilyTradeSourceQualityRound4Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradePrimarySourceRound2Exact as Primary2
import DASHI.Finance.TrumpFamilyTradeSourceQualityExact as Quality

------------------------------------------------------------------------
-- ROUND-FOUR PROPOSITION-INDEXED QUALITY
--
-- The December-18 Eric Trump / American Bitcoin purchase now has two distinct
-- source roles for the narrow transaction-existence/quantity proposition:
--
-- * SEC Schedule 13D/A No. 2: primary document, exact price/source-of-funds;
-- * Vicky Ge Huang / Dow Jones Newswires (WSJ live coverage), Jan. 5/6 2026:
--   independent report of the 285,000-share Dec. 18 purchase and resulting
--   >68m-share / 7.4% ownership state, attributed to regulatory filings.
--
-- The independent report is not promoted into exact price authority, ultimate
-- funding-source authority, policy causation, motive or legality.
------------------------------------------------------------------------

ericCashPurchaseIndependentArtifact : Source.SourceArtifact
ericCashPurchaseIndependentArtifact =
  Source.sourceArtifact
    "DowJones-WSJ-2026-01-05-Eric-ABTC-purchase"
    Source.derivedArtifact
    "https://www.itiger.com/news/2601389832"
    "Dow Jones Newswires / Wall Street Journal live coverage"

ericCashPurchaseIndependentCorroboration : Atlas.TradeEvidenceClaim
ericCashPurchaseIndependentCorroboration =
  Atlas.tradeEvidenceClaim
    "DowJones-2026-01-05-Eric-ABTC-285000"
    "Eric Trump"
    "American Bitcoin Corp. (ABTC)"
    Atlas.ownershipClaim
    "2025-12-18"
    "2026-01-05/06"
    "Vicky Ge Huang for Dow Jones/WSJ reported, citing regulatory filings, that Eric Trump purchased 285,000 American Bitcoin shares on December 18 and subsequently owned more than 68 million shares, approximately 7.4% of the company."
    Atlas.independentSynthesisSupport
    (Atlas.sourceCitation
      "Vicky Ge Huang / Dow Jones Newswires"
      "American Bitcoin Stock Jumps After Buying From Eric Trump, Other Insiders"
      "2026-01-05/06"
      "no DOI"
      "https://www.itiger.com/news/2601389832"
      Atlas.independentReporting)
    ericCashPurchaseIndependentArtifact
    "Independently corroborates the transaction date and 285,000-share purchase quantity and approximate resulting ownership state. Exact $1.7546 price and 'cash on hand' source-of-funds wording remain paid only by the SEC filing."
    false true false false

data EricCashPurchaseNarrowProposition : Set where
  eric-cash-purchase-narrow-proposition : EricCashPurchaseNarrowProposition

record EricCashPurchaseCorroborationPair : Set₁ where
  constructor eric-cash-purchase-corroboration-pair
  field
    primaryClaim : Atlas.TradeEvidenceClaim
    independentClaim : Atlas.TradeEvidenceClaim
    sameNarrowProposition : EricCashPurchaseNarrowProposition
    primaryPaid : Atlas.primarySourcePaid primaryClaim ≡ true
    independentPaid : Atlas.independentCorroborationPaid independentClaim ≡ true

open EricCashPurchaseCorroborationPair public

ericCashPurchaseCorroborationPair : EricCashPurchaseCorroborationPair
ericCashPurchaseCorroborationPair =
  eric-cash-purchase-corroboration-pair
    Primary2.ericAmericanBitcoinCashPurchase
    ericCashPurchaseIndependentCorroboration
    eric-cash-purchase-narrow-proposition
    refl refl

ericCashPurchaseQuality :
  Quality.ClaimEvidenceQuality Primary2.ericAmericanBitcoinCashPurchase
ericCashPurchaseQuality =
  Quality.claim-evidence-quality
    true true true true true true false false false

ericCashPurchasePromotionReady :
  Quality.PromotionReadyFor
    Primary2.ericAmericanBitcoinCashPurchase
    ericCashPurchaseQuality
ericCashPurchasePromotionReady =
  Quality.promotion-ready-for refl refl refl refl

------------------------------------------------------------------------
-- Narrow corroboration does not flow sideways to neighboring propositions.
------------------------------------------------------------------------

data ShareQuantityCorroborationAutomaticallyPaysExactPrice : Set where
data ShareQuantityCorroborationAutomaticallyPaysUltimateFundingSource : Set where
data ShareQuantityCorroborationAutomaticallyPaysPolicyCausation : Set where

corroborationDoesNotPayExactPrice :
  ShareQuantityCorroborationAutomaticallyPaysExactPrice → ⊥
corroborationDoesNotPayExactPrice ()

corroborationDoesNotPayUltimateFundingSource :
  ShareQuantityCorroborationAutomaticallyPaysUltimateFundingSource → ⊥
corroborationDoesNotPayUltimateFundingSource ()

corroborationDoesNotPayPolicyCausation :
  ShareQuantityCorroborationAutomaticallyPaysPolicyCausation → ⊥
corroborationDoesNotPayPolicyCausation ()

record TrumpFamilyTradeSourceQualityRound4Boundary : Set where
  constructor trump-family-trade-source-quality-round4-boundary
  field
    ericCashPurchasePrimaryPaid : Bool
    ericCashPurchaseIndependentNarrowCorroborationPaid : Bool
    exactPriceStillPrimaryOnly : Bool
    ultimateFundingSourceStillUnpaid : Bool
    policyCausationStillUnpaid : Bool
    sourceQualityRemainsPropositionIndexed : Bool

canonicalTrumpFamilyTradeSourceQualityRound4Boundary :
  TrumpFamilyTradeSourceQualityRound4Boundary
canonicalTrumpFamilyTradeSourceQualityRound4Boundary =
  trump-family-trade-source-quality-round4-boundary
    true true true true true true
