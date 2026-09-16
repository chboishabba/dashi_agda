module DASHI.Finance.TrumpFamilyTradePrimarySourceRound2Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradePrimarySourceExtensionExact as Primary

------------------------------------------------------------------------
-- ROUND-TWO PRIMARY TRANSACTION RECEIPTS
--
-- Exact event-level payments. Transaction identity != motive != policy
-- causation != MNPI != illegality != trade recommendation.
------------------------------------------------------------------------

donJrPSQHPrivatePlacementPersonalAllocation : Atlas.TradeEvidenceClaim
donJrPSQHPrivatePlacementPersonalAllocation =
  Atlas.tradeEvidenceClaim
    "PSQH-2026-08-13-DonJr-personal-allocation"
    "Donald J. Trump Jr."
    "PSQ Holdings, Inc. (PSQH)"
    Atlas.ownershipClaim
    "2026-08-13"
    "2026-08-18"
    "SEC Form 4 reports Donald J. Trump Jr. acquired 69,444 Class A common shares at $3.60 per share on August 13, 2026, with 891,847 shares beneficially owned directly after the reported transaction."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "U.S. Securities and Exchange Commission"
      "Form 4 — Statement of Changes in Beneficial Ownership, Donald J. Trump Jr. / PSQ Holdings, Inc., accession 0002016181-26-000005"
      "2026-08-18" "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1847064/000201618126000005/xslF345X06/form4-08182026_090843.xml"
      Atlas.beneficialOwnershipChange)
    (Atlas.secArtifact
      "0002016181-26-000005"
      "https://www.sec.gov/Archives/edgar/data/1847064/000201618126000005/xslF345X06/form4-08182026_090843.xml")
    "Pays Donald Jr.'s exact personal allocation, reported price and post-transaction beneficial-ownership quantity; it does not inherit the aggregate private-placement quantity or establish motive/causation."
    true false false false

donJrDominariOwnership : Atlas.TradeEvidenceClaim
donJrDominariOwnership =
  Atlas.tradeEvidenceClaim
    "DOMH-2026-06-01-DonJr-13G"
    "Donald J. Trump Jr."
    "Dominari Holdings Inc."
    Atlas.ownershipClaim
    "2026-05-22 ownership state"
    "2026-06-01"
    "SEC Schedule 13G reports Donald J. Trump Jr. beneficially owned 1,182,276 Dominari common shares. The filing separately excludes 216,138 shares issuable under certain warrants because beneficial-ownership limitations made those warrants not currently exercisable for the reported calculation."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "U.S. Securities and Exchange Commission"
      "Schedule 13G — Donald J. Trump Jr. / Dominari Holdings Inc., accession 0001213900-26-063164"
      "2026-06-01" "no DOI"
      "https://www.sec.gov/Archives/edgar/data/12239/000121390026063164/xslSCHEDULE_13G_X02/primary_doc.xml"
      Atlas.ownershipSchedule)
    (Atlas.secArtifact
      "0001213900-26-063164"
      "https://www.sec.gov/Archives/edgar/data/12239/000121390026063164/xslSCHEDULE_13G_X02/primary_doc.xml")
    "Pays the filed beneficial-ownership quantity and the warrant-exclusion qualifier only; beneficial ownership is not automatically an open-market trade or evidence of policy information."
    true false false false

------------------------------------------------------------------------
-- Eric Trump / American Bitcoin event sequence.
--
-- The initial 13D is owned by PrimarySourceRound3.  This round adds the two
-- subsequent event-level mechanisms that materially refine the ownership
-- history: no-consideration trust transfer and a later cash purchase.
------------------------------------------------------------------------

ericAmericanBitcoinTrustTransfer : Atlas.TradeEvidenceClaim
ericAmericanBitcoinTrustTransfer =
  Atlas.tradeEvidenceClaim
    "ABTC-2025-11-19-Eric-trust-transfer"
    "Eric Trump / Eric F. Trump Revocable Trust - 2015"
    "American Bitcoin Corp. (ABTC)"
    Atlas.trustOwnershipClaim
    "2025-11-19"
    "2025-11-20"
    "Schedule 13D Amendment No. 1 states that all American Bitcoin shares previously held by Eric Trump were transferred to the Eric F. Trump Revocable Trust - 2015 for no consideration; it identifies Eric Trump as trustee and beneficiary and states he may be deemed to beneficially own the trust-held shares."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "U.S. Securities and Exchange Commission"
      "Schedule 13D/A No. 1 — Eric Trump and Eric F. Trump Revocable Trust - 2015 / American Bitcoin Corp., accession 0001213900-25-113136"
      "2025-11-20" "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1755953/000121390025113136/xslSCHEDULE_13D_X01/primary_doc.xml"
      Atlas.ownershipSchedule)
    (Atlas.secArtifact
      "0001213900-25-113136"
      "https://www.sec.gov/Archives/edgar/data/1755953/000121390025113136/xslSCHEDULE_13D_X01/primary_doc.xml")
    "Pays the reported no-consideration transfer, trust relation and beneficial-ownership description only."
    true false false false

ericAmericanBitcoinCashPurchase : Atlas.TradeEvidenceClaim
ericAmericanBitcoinCashPurchase =
  Atlas.tradeEvidenceClaim
    "ABTC-2025-12-18-Eric-trust-cash-purchase"
    "Eric Trump / Eric F. Trump Revocable Trust - 2015"
    "American Bitcoin Corp. (ABTC)"
    Atlas.ownershipClaim
    "2025-12-18"
    "2025-12-22"
    "Schedule 13D Amendment No. 2 states that on December 18, 2025 the Eric F. Trump Revocable Trust - 2015 purchased 285,000 Class A shares of American Bitcoin Corp. at $1.7546 per share using cash on hand, increasing reported beneficial ownership to 68,432,664 shares."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "U.S. Securities and Exchange Commission"
      "Schedule 13D/A No. 2 — Eric Trump and Eric F. Trump Revocable Trust - 2015 / American Bitcoin Corp., accession 0001213900-25-124157"
      "2025-12-22" "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1755953/000121390025124157/xslSCHEDULE_13D_X01/primary_doc.xml"
      Atlas.beneficialOwnershipChange)
    (Atlas.secArtifact
      "0001213900-25-124157"
      "https://www.sec.gov/Archives/edgar/data/1755953/000121390025124157/xslSCHEDULE_13D_X01/primary_doc.xml")
    "Pays the exact reported purchase date, quantity, price, source-of-funds description ('cash on hand') and resulting beneficial-ownership total. It does not establish ultimate origin of the cash, policy causation, MNPI, motive, profit or legality."
    true false false false

------------------------------------------------------------------------
-- Transaction-mechanism typing.  A broad ownership claim is consumer-coarse;
-- the actual mechanism remains relevant to finance/trading/history consumers.
------------------------------------------------------------------------

data TransactionMode : Set where
  noConsiderationTrustTransfer : TransactionMode
  cashPurchase : TransactionMode
  paidPrivatePlacementAllocation : TransactionMode

record TypedTransactionClaim : Set₁ where
  constructor typed-transaction-claim
  field
    evidence : Atlas.TradeEvidenceClaim
    mode : TransactionMode
    modeReference : String

open TypedTransactionClaim public

ericTrustTransferTyped : TypedTransactionClaim
ericTrustTransferTyped = typed-transaction-claim
  ericAmericanBitcoinTrustTransfer noConsiderationTrustTransfer
  "13D/A No. 1 Item 3: transfer for no consideration"

ericCashPurchaseTyped : TypedTransactionClaim
ericCashPurchaseTyped = typed-transaction-claim
  ericAmericanBitcoinCashPurchase cashPurchase
  "13D/A No. 2 Item 3: 285,000 shares purchased for cash"

donJrPSQHPaidAllocationTyped : TypedTransactionClaim
donJrPSQHPaidAllocationTyped = typed-transaction-claim
  donJrPSQHPrivatePlacementPersonalAllocation paidPrivatePlacementAllocation
  "Form 4: 69,444 shares at $3.60"

trustTransferIsNotCashPurchase :
  noConsiderationTrustTransfer ≡ cashPurchase → ⊥
trustTransferIsNotCashPurchase ()

trump2025TechEquityPurchaseSeries : Atlas.TradeEvidenceClaim
trump2025TechEquityPurchaseSeries =
  Atlas.tradeEvidenceClaim
    "OGE-2026-Part7-tech-purchase-series"
    "Donald J. Trump"
    "Investment Account #8 — repeated public-equity purchases"
    Atlas.financialDisclosureClaim
    "2025 reporting period"
    "2026-06-29/30"
    "Part 7 of the certified annual disclosure reports repeated 2025 purchases in public-company securities including NVIDIA, Microsoft, Apple, Amazon, Alphabet, Meta, Tesla and other issuers, with transaction dates separately listed in the public form. This claim intentionally does not reconstruct amount-to-security row pairings beyond what is unambiguous in the parsed source."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "Donald J. Trump, filer; U.S. Office of Government Ethics"
      "Public Financial Disclosure Report (OGE Form 278e), 2026 annual report — Part 7, Investment Account #8 transaction pages"
      "OGE received 2026-06-29; reviewing-official comment 2026-06-30"
      "no DOI"
      "https://oge.box.com/shared/static/zycb5i2ny8kssm51uzqm8ygyq2zkpkqq.pdf"
      Atlas.annualFinancialDisclosure)
    Primary.ogeAnnualPDF
    "Pays existence and dates of the named Part-7 purchase events. It does not identify the trade decision-maker, connect the purchases to later policy, or promote parsed row order into an amount claim where the source extraction is ambiguous."
    true false false false

------------------------------------------------------------------------
-- Source-local non-promotion laws.
------------------------------------------------------------------------

data RepeatedSectorPurchasesAutomaticallyMeanPolicyTrade : Set where
data DirectorPrivatePlacementAutomaticallyMeansPreferentialTreatment : Set where
data BeneficialOwnershipAutomaticallyMeansSameAcquisitionMechanism : Set where
data CashOnHandAutomaticallyIdentifiesUltimateFundingSource : Set where

repeatedPurchasesDoNotCreatePolicyTrade : RepeatedSectorPurchasesAutomaticallyMeanPolicyTrade → ⊥
repeatedPurchasesDoNotCreatePolicyTrade ()

privatePlacementDoesNotProvePreferentialTreatment : DirectorPrivatePlacementAutomaticallyMeansPreferentialTreatment → ⊥
privatePlacementDoesNotProvePreferentialTreatment ()

ownershipDoesNotDetermineAcquisitionMechanism : BeneficialOwnershipAutomaticallyMeansSameAcquisitionMechanism → ⊥
ownershipDoesNotDetermineAcquisitionMechanism ()

cashOnHandDoesNotIdentifyUltimateFundingSource :
  CashOnHandAutomaticallyIdentifiesUltimateFundingSource → ⊥
cashOnHandDoesNotIdentifyUltimateFundingSource ()

record TrumpFamilyPrimarySourceRound2Boundary : Set where
  constructor trump-family-primary-source-round2-boundary
  field
    aggregatePlacementAndPersonalAllocationSeparated : Bool
    warrantQualifierRetained : Bool
    ogeTransactionSeriesPaidAtEventLevel : Bool
    parsedAmountAmbiguityNotSilentlyFilled : Bool
    ericTrustTransferAndCashPurchaseSeparated : Bool
    cashOnHandNotPromotedToUltimateCapitalSource : Bool
    transactionEvidenceDoesNotCreatePolicyCausation : Bool

canonicalTrumpFamilyPrimarySourceRound2Boundary : TrumpFamilyPrimarySourceRound2Boundary
canonicalTrumpFamilyPrimarySourceRound2Boundary =
  trump-family-primary-source-round2-boundary
    true true true true true true true
