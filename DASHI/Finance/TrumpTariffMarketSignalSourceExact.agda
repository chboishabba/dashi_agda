module DASHI.Finance.TrumpTariffMarketSignalSourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source

------------------------------------------------------------------------
-- APRIL 9 2025 TARIFF / PUBLIC-SIGNAL / MARKET SEQUENCE
--
-- Sources:
-- * Office of Senator Adam Schiff / Sen. Ruben Gallego,
--   "Sens. Schiff, Gallego Demand Investigation into Potential Insider Trading
--    and Corruption Ahead of Trump Tariff Pause", 10 April 2025, no DOI.
-- * U.S. Senate Committee on Banking, Housing, and Urban Affairs,
--   Warren, Schumer et al., request to SEC concerning possible tariff-market
--   manipulation / insider trading, 11 April 2025, no DOI.
-- * Reuters, "In stunning U-turn, Trump walks back some tariffs, triggering
--   historic market rally", 9 April 2025, no DOI.
--
-- The first two are attributed oversight requests, not findings. Reuters pays
-- independent reporting on the policy reversal / market response, not hidden
-- knowledge, trade identity, motive or illegality.
------------------------------------------------------------------------

data TariffMarketClaimKind : Set where
  publicSignalClaim : TariffMarketClaimKind
  policyAnnouncementClaim : TariffMarketClaimKind
  marketOutcomeClaim : TariffMarketClaimKind
  investigationRequestClaim : TariffMarketClaimKind

data TariffMarketSupportMode : Set where
  officialDocumentarySupport : TariffMarketSupportMode
  independentReportingSupport : TariffMarketSupportMode
  attributedOversightConcern : TariffMarketSupportMode

record TariffMarketClaim : Set₁ where
  constructor tariff-market-claim
  field
    claimId : String
    eventTimeReference : String
    publicationTimeReference : String
    proposition : String
    claimKind : TariffMarketClaimKind
    supportMode : TariffMarketSupportMode
    source : Source.SourceArtifact
    sourceTitle : String
    supportScope : String
    primaryOrOfficialSourcePaid : Bool
    independentCorroborationPaid : Bool
    hiddenKnowledgePaid : Bool
    tradeIdentityPaid : Bool
    legalFindingPaid : Bool

open TariffMarketClaim public

schiffGallegoArtifact : Source.SourceArtifact
schiffGallegoArtifact =
  Source.sourceArtifact
    "Schiff-Gallego-2025-04-10-tariff-letter"
    Source.documentaryArtifact
    "https://www.schiff.senate.gov/news/press-releases/news-sens-schiff-gallego-demand-investigation-into-potential-insider-trading-and-corruption-ahead-of-trump-tariff-pause/"
    "United States Senate"

senateBankingArtifact : Source.SourceArtifact
senateBankingArtifact =
  Source.sourceArtifact
    "Senate-Banking-2025-04-11-tariff-SEC-request"
    Source.documentaryArtifact
    "https://www.banking.senate.gov/newsroom/minority/warren-schumer-senate-colleagues-call-on-sec-to-launch-investigation-into-possible-trump-tariff-market-manipulation-insider-trading"
    "United States Senate Committee on Banking, Housing, and Urban Affairs"

reutersApril9Artifact : Source.SourceArtifact
reutersApril9Artifact =
  Source.sourceArtifact
    "Reuters-2025-04-09-tariff-pause-rally"
    Source.derivedArtifact
    "https://www.reuters.com/world/trumps-latest-tariffs-loom-set-deepen-global-trade-war-2025-04-09/"
    "Reuters"

buyPost : TariffMarketClaim
buyPost = tariff-market-claim
  "Trump-Truth-2025-04-09-0937-buy"
  "2025-04-09 09:37 ET, as quoted by the Senate sources"
  "2025-04-09 public post"
  "Official Senate correspondence quotes President Trump's Truth Social post: THIS IS A GREAT TIME TO BUY!!! DJT."
  publicSignalClaim
  officialDocumentarySupport
  schiffGallegoArtifact
  "Sens. Schiff, Gallego Demand Investigation into Potential Insider Trading and Corruption Ahead of Trump Tariff Pause"
  "Pays the quoted public post and reported timestamp as reproduced in official Senate correspondence; does not prove trading, recipients' interpretation, advance knowledge, manipulation or motive."
  true false false false false

tariffPauseAnnouncement : TariffMarketClaim
tariffPauseAnnouncement = tariff-market-claim
  "Trump-Truth-2025-04-09-1318-tariff-pause"
  "2025-04-09 13:18 ET, as reported/quoted by the Senate sources"
  "2025-04-09 public announcement"
  "Official Senate correspondence records that President Trump announced a pause on most of the recently imposed tariffs at 1:18 PM, roughly four hours after the buy post."
  policyAnnouncementClaim
  officialDocumentarySupport
  schiffGallegoArtifact
  "Sens. Schiff, Gallego Demand Investigation into Potential Insider Trading and Corruption Ahead of Trump Tariff Pause"
  "Pays the reported public policy-announcement time and sequence only; not preannouncement knowledge or trade causation."
  true true false false false

marketRally : TariffMarketClaim
marketRally = tariff-market-claim
  "US-market-2025-04-09-rally"
  "2025-04-09 regular trading session / close"
  "2025-04-09"
  "Reuters reported a historic U.S. equity rally after the tariff reversal; Senate correspondence records the S&P 500 closing 9.5 percent higher."
  marketOutcomeClaim
  independentReportingSupport
  reutersApril9Artifact
  "In stunning U-turn, Trump walks back some tariffs, triggering historic market rally"
  "Pays the observed market response and temporal ordering relative to the public announcement; does not identify any beneficiary trade or prove a causal effect for a particular portfolio."
  false true false false false

senateInvestigationRequest : TariffMarketClaim
senateInvestigationRequest = tariff-market-claim
  "Senate-2025-04-11-SEC-tariff-request"
  "2025-04-11"
  "2025-04-11"
  "A group of U.S. senators asked the SEC to investigate whether President Trump, family members, officials, donors or other insiders traded on advance knowledge of tariff-policy changes."
  investigationRequestClaim
  attributedOversightConcern
  senateBankingArtifact
  "Warren, Schumer, Senate Colleagues Call on SEC to Launch Investigation into Possible Trump Tariff Market Manipulation, Insider Trading"
  "Pays the existence and scope of the attributed investigation request only. It is not an SEC finding and does not establish that any named person traded on material nonpublic information."
  true false false false false

------------------------------------------------------------------------
-- Sequence is observable; the contested hidden-information edges are not.
------------------------------------------------------------------------

record PublicSequence : Set₁ where
  constructor public-sequence
  field
    signal policy market : TariffMarketClaim
    signalPrecedesPolicyReference : String
    policyPrecedesCloseReference : String
    sequenceCreatesHiddenKnowledge : Bool
    sequenceCreatesHiddenKnowledgeIsFalse : sequenceCreatesHiddenKnowledge ≡ false
    sequenceCreatesTradeIdentity : Bool
    sequenceCreatesTradeIdentityIsFalse : sequenceCreatesTradeIdentity ≡ false

open PublicSequence public

canonicalApril9Sequence : PublicSequence
canonicalApril9Sequence =
  public-sequence buyPost tariffPauseAnnouncement marketRally
    "09:37 ET public buy post precedes 13:18 ET public tariff-pause announcement"
    "13:18 ET public announcement precedes the 16:00 ET regular-market close"
    false refl false refl

data SequenceAutomaticallyProvesInsiderTrading : Set where
data MarketMoveAutomaticallyIdentifiesBeneficiary : Set where
data OversightRequestAutomaticallyProvesViolation : Set where

sequenceDoesNotProveInsiderTrading : SequenceAutomaticallyProvesInsiderTrading → ⊥
sequenceDoesNotProveInsiderTrading ()

marketMoveDoesNotIdentifyBeneficiary : MarketMoveAutomaticallyIdentifiesBeneficiary → ⊥
marketMoveDoesNotIdentifyBeneficiary ()

oversightRequestDoesNotProveViolation : OversightRequestAutomaticallyProvesViolation → ⊥
oversightRequestDoesNotProveViolation ()
