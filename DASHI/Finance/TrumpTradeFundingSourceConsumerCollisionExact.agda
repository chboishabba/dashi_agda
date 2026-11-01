module DASHI.Finance.TrumpTradeFundingSourceConsumerCollisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradePrimarySourceRound3Exact as Round3
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- REPORTED-TRADE / FUNDING-SOURCE CONSUMER COLLISION
--
-- The OGE 278-T pays the coarse proposition that a reported Coinbase sale
-- occurred on the disclosed date and in the disclosed value band.  It does not
-- report the capital source behind that position, nor who selected the trade.
--
-- This file makes that non-identifiability constructive: multiple fine worlds
-- project to the same source-paid reported transaction while differing on the
-- hidden funding-source and decision-maker coordinates.
------------------------------------------------------------------------

data ReportedTrade : Set where
  trumpCoinbaseSale20260212 : ReportedTrade

data FundingSource : Set where
  cryptoRelatedProceeds : FundingSource
  otherPortfolioCapital : FundingSource
  unknownCapitalSource : FundingSource

data DecisionMaker : Set where
  filerDirected : DecisionMaker
  adviserDirected : DecisionMaker
  unknownDecisionMaker : DecisionMaker

record FineTradeWorld : Set where
  constructor fine-trade-world
  field
    reportedTrade : ReportedTrade
    fundingSource : FundingSource
    decisionMaker : DecisionMaker
    fineWorldReference : String

open FineTradeWorld public

projectReportedTrade : FineTradeWorld → ReportedTrade
projectReportedTrade = reportedTrade

------------------------------------------------------------------------
-- The actual documentary anchor is source-bounded and shared by every candidate
-- fine world below.  The candidate worlds are mathematical alternatives, not
-- empirical claims about which world obtained.
------------------------------------------------------------------------

reportedTradeEvidence : Atlas.TradeEvidenceClaim
reportedTradeEvidence = Round3.trumpCoinbaseSale20260212

reportedTradeEvidenceIsPrimary :
  Atlas.primarySourcePaid reportedTradeEvidence ≡ true
reportedTradeEvidenceIsPrimary = refl

cryptoFundedCandidate : FineTradeWorld
cryptoFundedCandidate =
  fine-trade-world
    trumpCoinbaseSale20260212
    cryptoRelatedProceeds
    unknownDecisionMaker
    "candidate fine world only: crypto-related proceeds supplied capital; not selected by current evidence"

portfolioFundedCandidate : FineTradeWorld
portfolioFundedCandidate =
  fine-trade-world
    trumpCoinbaseSale20260212
    otherPortfolioCapital
    unknownDecisionMaker
    "candidate fine world only: other portfolio capital supplied capital; not selected by current evidence"

adviserSelectedCandidate : FineTradeWorld
adviserSelectedCandidate =
  fine-trade-world
    trumpCoinbaseSale20260212
    unknownCapitalSource
    adviserDirected
    "candidate fine world only: adviser selected trade; not selected by current evidence"

sameReportedTradeAcrossFundingCandidates :
  projectReportedTrade cryptoFundedCandidate
  ≡ projectReportedTrade portfolioFundedCandidate
sameReportedTradeAcrossFundingCandidates = refl

fundingSourceDiffersAcrossSameReportedTrade :
  fundingSource cryptoFundedCandidate
  ≡ fundingSource portfolioFundedCandidate → ⊥
fundingSourceDiffersAcrossSameReportedTrade ()

sameReportedTradeAcrossDecisionCandidates :
  projectReportedTrade cryptoFundedCandidate
  ≡ projectReportedTrade adviserSelectedCandidate
sameReportedTradeAcrossDecisionCandidates = refl

decisionMakerDiffersAcrossSameReportedTrade :
  decisionMaker cryptoFundedCandidate
  ≡ decisionMaker adviserSelectedCandidate → ⊥
decisionMakerDiffersAcrossSameReportedTrade ()

------------------------------------------------------------------------
-- Reopening receipt.
------------------------------------------------------------------------

record TradeHiddenReceipt : Set where
  constructor trade-hidden-receipt
  field
    retainedFundingSource : FundingSource
    retainedDecisionMaker : DecisionMaker
    receiptReference : String

open TradeHiddenReceipt public

receiptFor : FineTradeWorld → TradeHiddenReceipt
receiptFor world =
  trade-hidden-receipt
    (fundingSource world)
    (decisionMaker world)
    (fineWorldReference world)

reopen : ReportedTrade → TradeHiddenReceipt → FineTradeWorld
reopen trade receipt =
  fine-trade-world
    trade
    (retainedFundingSource receipt)
    (retainedDecisionMaker receipt)
    (receiptReference receipt)

reopenExact : (world : FineTradeWorld) →
  reopen (projectReportedTrade world) (receiptFor world) ≡ world
reopenExact (fine-trade-world trade funding decision ref) = refl

------------------------------------------------------------------------
-- Consumer-specific sufficiency.
------------------------------------------------------------------------

data Consumer : Set where
  reportedEventConsumer : Consumer
  fundingSourceConsumer : Consumer
  decisionMakerConsumer : Consumer

record ConsumerAdequacyBoundary : Set where
  constructor consumer-adequacy-boundary
  field
    filingPaysReportedEventConsumer : Bool
    filingPaysFundingSourceConsumer : Bool
    filingPaysDecisionMakerConsumer : Bool
    fundingResidualRequiredForFundingConsumer : Bool
    decisionResidualRequiredForDecisionConsumer : Bool

canonicalConsumerAdequacyBoundary : ConsumerAdequacyBoundary
canonicalConsumerAdequacyBoundary =
  consumer-adequacy-boundary true false false true true

------------------------------------------------------------------------
-- Attribution boundaries.
------------------------------------------------------------------------

data ReutersCryptoSynthesisSelectsFundingWorldPermission : Set where
data FamilyBusinessIncomeSelectsFundingWorldPermission : Set where
data FiledTradeSelectsDecisionMakerPermission : Set where
data CandidateWorldIsEmpiricalClaimPermission : Set where

reutersSynthesisDoesNotSelectFundingWorld :
  ReutersCryptoSynthesisSelectsFundingWorldPermission → ⊥
reutersSynthesisDoesNotSelectFundingWorld ()

familyBusinessIncomeDoesNotSelectFundingWorld :
  FamilyBusinessIncomeSelectsFundingWorldPermission → ⊥
familyBusinessIncomeDoesNotSelectFundingWorld ()

filedTradeDoesNotSelectDecisionMaker :
  FiledTradeSelectsDecisionMakerPermission → ⊥
filedTradeDoesNotSelectDecisionMaker ()

candidateWorldDoesNotBecomeEmpiricalClaim :
  CandidateWorldIsEmpiricalClaimPermission → ⊥
candidateWorldDoesNotBecomeEmpiricalClaim ()

record TrumpTradeFundingSourceCollisionBoundary : Set where
  constructor trump-trade-funding-source-collision-boundary
  field
    reportedTransactionPaid : Bool
    fundingSourceNotRecoveredFromFiling : Bool
    decisionMakerNotRecoveredFromFiling : Bool
    sameCoarseTradeHasDistinctFundingCandidates : Bool
    hiddenReceiptReopensFineWorldExactly : Bool
    secondarySynthesisDoesNotSelectActualFineWorld : Bool
    candidateFineWorldsAreNotEmpiricalAssertions : Bool

canonicalTrumpTradeFundingSourceCollisionBoundary :
  TrumpTradeFundingSourceCollisionBoundary
canonicalTrumpTradeFundingSourceCollisionBoundary =
  trump-trade-funding-source-collision-boundary
    true true true true true true true
