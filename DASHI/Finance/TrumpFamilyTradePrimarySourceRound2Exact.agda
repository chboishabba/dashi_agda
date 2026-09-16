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
-- These are exact event-level payments for claims that were previously present
-- only as aggregate/private-placement or annual-ledger observations.  They are
-- deliberately narrow: transaction identity != motive != policy causation !=
-- MNPI != illegality != trade recommendation.
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
      "2026-08-18"
      "no DOI"
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
      "2026-06-01"
      "no DOI"
      "https://www.sec.gov/Archives/edgar/data/12239/000121390026063164/xslSCHEDULE_13G_X02/primary_doc.xml"
      Atlas.ownershipSchedule)
    (Atlas.secArtifact
      "0001213900-26-063164"
      "https://www.sec.gov/Archives/edgar/data/12239/000121390026063164/xslSCHEDULE_13G_X02/primary_doc.xml")
    "Pays the filed beneficial-ownership quantity and the warrant-exclusion qualifier only; beneficial ownership is not automatically an open-market trade or evidence of policy information."
    true false false false

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

repeatedPurchasesDoNotCreatePolicyTrade :
  RepeatedSectorPurchasesAutomaticallyMeanPolicyTrade → ⊥
repeatedPurchasesDoNotCreatePolicyTrade ()

privatePlacementDoesNotProvePreferentialTreatment :
  DirectorPrivatePlacementAutomaticallyMeansPreferentialTreatment → ⊥
privatePlacementDoesNotProvePreferentialTreatment ()

ownershipDoesNotDetermineAcquisitionMechanism :
  BeneficialOwnershipAutomaticallyMeansSameAcquisitionMechanism → ⊥
ownershipDoesNotDetermineAcquisitionMechanism ()

record TrumpFamilyPrimarySourceRound2Boundary : Set where
  constructor trump-family-primary-source-round2-boundary
  field
    aggregatePlacementAndPersonalAllocationSeparated : Bool
    warrantQualifierRetained : Bool
    ogeTransactionSeriesPaidAtEventLevel : Bool
    parsedAmountAmbiguityNotSilentlyFilled : Bool
    transactionEvidenceDoesNotCreatePolicyCausation : Bool

canonicalTrumpFamilyPrimarySourceRound2Boundary :
  TrumpFamilyPrimarySourceRound2Boundary
canonicalTrumpFamilyPrimarySourceRound2Boundary =
  trump-family-primary-source-round2-boundary true true true true true
