module DASHI.Finance.TrumpFamilyTradeSourceAtlasRound2Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- TRUMP-FAMILY TRADE SOURCE ATLAS — ROUND TWO
--
-- Extension of the canonical claim/source vocabulary.  This tranche prefers
-- exact transaction sequences from SEC filings over coarse ownership summaries.
-- No source edge below establishes MNPI, insider trading, policy causation,
-- motive, legal liability, or a profitable trading strategy.
--
-- Source provenance (no DOI for any item):
-- * U.S. SEC, Schedule 13D, Eric Trump / American Bitcoin Corp., filed
--   2025-09-03, accession 0000950170-25-114071.
-- * U.S. SEC, Schedule 13D/A No. 1, Eric Trump and Eric F. Trump Revocable
--   Trust - 2015 / American Bitcoin Corp., filed 2025-11-20,
--   accession 0001213900-25-113136.
-- * U.S. SEC, Schedule 13D/A No. 2, same reporting persons / American Bitcoin
--   Corp., filed 2025-12-22, accession 0001213900-25-124157.
-- * U.S. SEC, Form 4, Donald J. Trump Jr. / PSQ Holdings, Inc., filed
--   2026-08-18, reporting document 0002016181-26-000005.
-- * Reuters, "Trump invested crypto gains in stocks and bonds, filings show",
--   2026-07-13, retained only as independent synthesis.
------------------------------------------------------------------------

ericAmericanBitcoinInitial13D : Atlas.TradeEvidenceClaim
ericAmericanBitcoinInitial13D = Atlas.tradeEvidenceClaim
  "ABTC-2025-09-03-Eric-Trump-initial-13D"
  "Eric Trump"
  "American Bitcoin Corp. (ABTC)"
  Atlas.ownershipClaim
  "2025-09-03"
  "2025-09-03"
  "Eric Trump's initial Schedule 13D reports 68,147,664 shares beneficially owned, 7.5% under the filing's stated denominator. Item 3 states that the issuer issued those shares at the September 3, 2025 merger closing; Item 4 states that the reporting person held them for general investment purposes."
  Atlas.directDocumentarySupport
  (Atlas.sourceCitation
    "U.S. Securities and Exchange Commission"
    "Schedule 13D — Eric Trump / American Bitcoin Corp., accession 0000950170-25-114071"
    "2025-09-03" "no DOI"
    "https://www.sec.gov/Archives/edgar/data/1755953/000095017025114071/xslSCHEDULE_13D_X01/primary_doc.xml"
    Atlas.ownershipSchedule)
  (Atlas.secArtifact "0000950170-25-114071"
    "https://www.sec.gov/Archives/edgar/data/1755953/000095017025114071/xslSCHEDULE_13D_X01/primary_doc.xml")
  "Supports the filing's ownership quantities, merger-closing issuance and stated investment-purpose description only."
  true false false false

ericAmericanBitcoinTrustTransfer : Atlas.TradeEvidenceClaim
ericAmericanBitcoinTrustTransfer = Atlas.tradeEvidenceClaim
  "ABTC-2025-11-19-Eric-trust-transfer"
  "Eric Trump / Eric F. Trump Revocable Trust - 2015"
  "American Bitcoin Corp. (ABTC)"
  Atlas.trustOwnershipClaim
  "2025-11-19" "2025-11-20"
  "Schedule 13D Amendment No. 1 states that all American Bitcoin shares previously held by Eric Trump were transferred to the Eric F. Trump Revocable Trust - 2015 for no consideration; it identifies Eric Trump as trustee and beneficiary and states he may be deemed to beneficially own the trust-held shares."
  Atlas.directDocumentarySupport
  (Atlas.sourceCitation
    "U.S. Securities and Exchange Commission"
    "Schedule 13D/A No. 1 — Eric Trump and Eric F. Trump Revocable Trust - 2015 / American Bitcoin Corp., accession 0001213900-25-113136"
    "2025-11-20" "no DOI"
    "https://www.sec.gov/Archives/edgar/data/1755953/000121390025113136/xslSCHEDULE_13D_X01/primary_doc.xml"
    Atlas.ownershipSchedule)
  (Atlas.secArtifact "0001213900-25-113136"
    "https://www.sec.gov/Archives/edgar/data/1755953/000121390025113136/xslSCHEDULE_13D_X01/primary_doc.xml")
  "Supports only the reported no-consideration transfer, trust relation and resulting beneficial-ownership description."
  true false false false

ericAmericanBitcoinCashPurchase : Atlas.TradeEvidenceClaim
ericAmericanBitcoinCashPurchase = Atlas.tradeEvidenceClaim
  "ABTC-2025-12-18-Eric-trust-cash-purchase"
  "Eric Trump / Eric F. Trump Revocable Trust - 2015"
  "American Bitcoin Corp. (ABTC)"
  Atlas.ownershipClaim
  "2025-12-18" "2025-12-22"
  "Schedule 13D Amendment No. 2 states that on December 18, 2025 the Eric F. Trump Revocable Trust - 2015 purchased 285,000 Class A shares of American Bitcoin Corp. at $1.7546 per share using cash on hand, increasing reported beneficial ownership to 68,432,664 shares."
  Atlas.directDocumentarySupport
  (Atlas.sourceCitation
    "U.S. Securities and Exchange Commission"
    "Schedule 13D/A No. 2 — Eric Trump and Eric F. Trump Revocable Trust - 2015 / American Bitcoin Corp., accession 0001213900-25-124157"
    "2025-12-22" "no DOI"
    "https://www.sec.gov/Archives/edgar/data/1755953/000121390025124157/xslSCHEDULE_13D_X01/primary_doc.xml"
    Atlas.beneficialOwnershipChange)
  (Atlas.secArtifact "0001213900-25-124157"
    "https://www.sec.gov/Archives/edgar/data/1755953/000121390025124157/xslSCHEDULE_13D_X01/primary_doc.xml")
  "Supports the exact reported purchase date, quantity, price, source of funds and resulting ownership total; not policy causation, MNPI, motive, profit or legality."
  true false false false

donJrPSQHPaidPurchase2026Aug13 : Atlas.TradeEvidenceClaim
donJrPSQHPaidPurchase2026Aug13 = Atlas.tradeEvidenceClaim
  "PSQH-2026-08-13-paid-purchase"
  "Donald J. Trump Jr."
  "PSQ Holdings, Inc. (PSQH)"
  Atlas.ownershipClaim
  "2026-08-13" "2026-08-18"
  "SEC Form 4 reports Donald J. Trump Jr. acquired 69,444 shares of PSQ Holdings Class A common stock on August 13, 2026 at $3.60 per share, with 891,847 securities reported beneficially owned following the transaction."
  Atlas.directDocumentarySupport
  (Atlas.sourceCitation
    "U.S. Securities and Exchange Commission"
    "Form 4 — Donald J. Trump Jr. / PSQ Holdings, Inc., reporting document 0002016181-26-000005"
    "2026-08-18" "no DOI"
    "https://www.sec.gov/Archives/edgar/data/1847064/000201618126000005/xslF345X06/form4-08182026_090843.xml"
    Atlas.beneficialOwnershipChange)
  (Atlas.secArtifact "0002016181-26-000005"
    "https://www.sec.gov/Archives/edgar/data/1847064/000201618126000005/xslF345X06/form4-08182026_090843.xml")
  "Supports the reported paid acquisition and post-transaction beneficial-ownership count only."
  true false false false

reutersArtifact : Source.SourceArtifact
reutersArtifact = Source.sourceArtifact
  "Reuters-2026-07-13-Trump-financial-disclosure-synthesis"
  Source.documentaryArtifact
  "https://www.reuters.com/legal/government/trump-invested-crypto-gains-stocks-bonds-filings-show-2026-07-13/"
  "Reuters"

trumpCryptoAllocationReuters2026 : Atlas.TradeEvidenceClaim
trumpCryptoAllocationReuters2026 = Atlas.tradeEvidenceClaim
  "Reuters-2026-07-13-Trump-crypto-gains-traditional-assets"
  "Donald J. Trump"
  "2026 financial disclosure / crypto and traditional holdings"
  Atlas.financialDisclosureClaim
  "2025 reporting period" "2026-07-13"
  "Reuters reported, based on President Trump's 2026 financial disclosures, that large 2025 crypto-related income coexisted with substantial traditional stock and bond holdings. This remains independent synthesis; primary disclosures retain authority for individual holdings and transactions."
  Atlas.independentSynthesisSupport
  (Atlas.sourceCitation
    "Reuters"
    "Trump invested crypto gains in stocks and bonds, filings show"
    "2026-07-13" "no DOI"
    "https://www.reuters.com/legal/government/trump-invested-crypto-gains-stocks-bonds-filings-show-2026-07-13/"
    Atlas.independentReporting)
  reutersArtifact
  "Supports Reuters' attributed synthesis only; it does not replace primary transaction/disclosure documents and does not support a motive claim."
  false true false false

------------------------------------------------------------------------
-- Typed transaction-mode layer: unlike TradeClaimKind, these modes distinguish
-- the concrete transaction mechanism needed by the trading consumer.
------------------------------------------------------------------------

data TransactionMode : Set where
  mergerIssuance : TransactionMode
  noConsiderationTrustTransfer : TransactionMode
  cashMarketPurchase : TransactionMode
  paidIssuerPurchase : TransactionMode

record TypedTransactionClaim : Set₁ where
  constructor typedTransactionClaim
  field
    evidence : Atlas.TradeEvidenceClaim
    mode : TransactionMode
    modeReference : String

open TypedTransactionClaim public

ericInitialTyped : TypedTransactionClaim
ericInitialTyped = typedTransactionClaim ericAmericanBitcoinInitial13D mergerIssuance
  "Schedule 13D Item 3: merger-closing issuance"

ericTrustTransferTyped : TypedTransactionClaim
ericTrustTransferTyped = typedTransactionClaim ericAmericanBitcoinTrustTransfer noConsiderationTrustTransfer
  "Schedule 13D/A No. 1 Item 3: transfer for no consideration"

ericCashPurchaseTyped : TypedTransactionClaim
ericCashPurchaseTyped = typedTransactionClaim ericAmericanBitcoinCashPurchase cashMarketPurchase
  "Schedule 13D/A No. 2 Item 3: 285,000-share cash purchase"

donJrPSQHPurchaseTyped : TypedTransactionClaim
donJrPSQHPurchaseTyped = typedTransactionClaim donJrPSQHPaidPurchase2026Aug13 paidIssuerPurchase
  "Form 4: 69,444 shares acquired at $3.60"

mergerIssuanceIsNotCashPurchase : mergerIssuance ≡ cashMarketPurchase → ⊥
mergerIssuanceIsNotCashPurchase ()

trustTransferIsNotCashPurchase : noConsiderationTrustTransfer ≡ cashMarketPurchase → ⊥
trustTransferIsNotCashPurchase ()

record TrumpFamilyTradeSourceRound2Boundary : Set where
  constructor trump-family-trade-source-round2-boundary
  field
    exactTransactionSequenceRetained : Bool
    ownershipSnapshotDistinctFromPaidPurchase : Bool
    trustTransferDistinctFromPaidPurchase : Bool
    secondarySynthesisDoesNotReplacePrimary : Bool
    transactionTimingProvesMNPI : Bool
    familyRelationTransportsKnowledge : Bool

canonicalTrumpFamilyTradeSourceRound2Boundary : TrumpFamilyTradeSourceRound2Boundary
canonicalTrumpFamilyTradeSourceRound2Boundary =
  trump-family-trade-source-round2-boundary true true true true false false
