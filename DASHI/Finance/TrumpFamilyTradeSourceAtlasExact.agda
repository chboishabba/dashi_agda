module DASHI.Finance.TrumpFamilyTradeSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source

------------------------------------------------------------------------
-- TRUMP-FAMILY TRADE / MARKET-INTEREST SOURCE ATLAS
--
-- Claim-level documentary layer only.  Transaction/ownership records, company
-- product disclosures, annual financial disclosure and attributed regulatory
-- concerns remain separate.  None of these source edges by itself proves
-- insider trading, corruption, motive, illegality, material nonpublic
-- information, policy causation or a profitable trade.
------------------------------------------------------------------------

data TradeEvidenceKind : Set where
  annualFinancialDisclosure : TradeEvidenceKind
  beneficialOwnershipChange : TradeEvidenceKind
  ownershipSchedule : TradeEvidenceKind
  companyProductDisclosure : TradeEvidenceKind
  independentReporting : TradeEvidenceKind
  attributedRegulatoryConcern : TradeEvidenceKind

data SupportMode : Set where
  directDocumentarySupport : SupportMode
  issuerStatementSupport : SupportMode
  independentSynthesisSupport : SupportMode
  attributedConcernSupport : SupportMode

data TradeClaimKind : Set where
  ownershipClaim : TradeClaimKind
  restrictedStockClaim : TradeClaimKind
  warrantExerciseClaim : TradeClaimKind
  financialDisclosureClaim : TradeClaimKind
  marketDataProductClaim : TradeClaimKind
  informationLatencyClaim : TradeClaimKind
  regulatoryConcernClaim : TradeClaimKind

record SourceCitation : Set where
  constructor sourceCitation
  field
    authorOrInstitution : String
    title : String
    publicationDate : String
    doi : String
    url : String
    sourceKind : TradeEvidenceKind

open SourceCitation public

record TradeEvidenceClaim : Set₁ where
  constructor tradeEvidenceClaim
  field
    claimId : String
    subject : String
    issuerOrObject : String
    claimKind : TradeClaimKind
    eventDate : String
    disclosureDate : String
    proposition : String
    supportMode : SupportMode
    citation : SourceCitation
    sourceArtifact : Source.SourceArtifact
    supportScope : String
    primarySourcePaid : Bool
    independentCorroborationPaid : Bool
    legalConclusionPaid : Bool
    motiveClaimPaid : Bool

open TradeEvidenceClaim public

secArtifact : String → String → Source.SourceArtifact
secArtifact accession url =
  Source.sourceArtifact accession Source.documentaryArtifact url
    "U.S. Securities and Exchange Commission EDGAR"

ogeArtifact : Source.SourceArtifact
ogeArtifact =
  Source.sourceArtifact
    "Trump-2026-certified-annual-financial-disclosure"
    Source.documentaryArtifact
    "https://www2.oge.gov/web/oge.nsf/Resources/Now%2BAvailable%3A%2BThe%2BPresident%E2%80%99s%2Band%2BVice%2BPresident%E2%80%99s%2Bcertified%2Bannual%2Bfinancial%2Bdisclosure%2Breports"
    "U.S. Office of Government Ethics"

------------------------------------------------------------------------
-- Primary securities/disclosure observations acquired in this tranche.
------------------------------------------------------------------------

donJrTMTGRSU : TradeEvidenceClaim
donJrTMTGRSU = tradeEvidenceClaim
  "DJT-2026-06-19-RSU"
  "Donald J. Trump Jr."
  "Trump Media & Technology Group Corp. (DJT)"
  restrictedStockClaim
  "2026-06-19"
  "2026-06-23"
  "SEC Form 4 reports acquisition of 23,600 restricted stock units/shares at reported price $0; reporting person is identified as director and 10% owner. The form separately reports 114,750,000 shares held indirectly through the Donald J. Trump Revocable Trust."
  directDocumentarySupport
  (sourceCitation
    "U.S. Securities and Exchange Commission"
    "Form 4 — Statement of Changes in Beneficial Ownership, Donald J. Trump Jr. / Trump Media & Technology Group Corp., accession 0001437749-26-021434"
    "2026-06-23"
    "no DOI"
    "https://www.sec.gov/Archives/edgar/data/1849635/000143774926021434/xslF345X06/rdgdoc.xml"
    beneficialOwnershipChange)
  (secArtifact "0001437749-26-021434"
    "https://www.sec.gov/Archives/edgar/data/1849635/000143774926021434/xslF345X06/rdgdoc.xml")
  "Supports the reported ownership transaction and relationship-to-issuer fields only."
  true false false false

donJrPSQHRSU : TradeEvidenceClaim
donJrPSQHRSU = tradeEvidenceClaim
  "PSQH-2026-07-09-RSU"
  "Donald J. Trump Jr."
  "PSQ Holdings, Inc. (PSQH)"
  restrictedStockClaim
  "2026-07-09"
  "2026-07-10"
  "SEC Form 4 reports acquisition of 125,000 unvested restricted stock units at reported price $0, vesting July 9, 2027 subject to continuous service; reporting person is identified as director."
  directDocumentarySupport
  (sourceCitation
    "U.S. Securities and Exchange Commission"
    "Form 4 — Statement of Changes in Beneficial Ownership, Donald J. Trump Jr. / PSQ Holdings, Inc., accession 0002016181-26-000003"
    "2026-07-10"
    "no DOI"
    "https://www.sec.gov/Archives/edgar/data/1847064/000201618126000003/xslF345X06/form4-07102026_080701.xml"
    beneficialOwnershipChange)
  (secArtifact "0002016181-26-000003"
    "https://www.sec.gov/Archives/edgar/data/1847064/000201618126000003/xslF345X06/form4-07102026_080701.xml")
  "Supports the reported RSU award and issuer-role fields only."
  true false false false

donJrGrabAGunVesting : TradeEvidenceClaim
donJrGrabAGunVesting = tradeEvidenceClaim
  "PEW-2026-06-23-RSU-vesting"
  "Donald J. Trump Jr."
  "GrabAGun Digital Holdings Inc. (PEW)"
  restrictedStockClaim
  "2026-06-23"
  "2026-06-24"
  "SEC Form 4 reports conversion/vesting of 11,433 restricted stock units into common stock on a one-for-one basis, bringing reported direct beneficial ownership to 311,433 shares."
  directDocumentarySupport
  (sourceCitation
    "U.S. Securities and Exchange Commission"
    "Form 4 — Statement of Changes in Beneficial Ownership, Donald J. Trump Jr. / GrabAGun Digital Holdings Inc., accession 0001213900-26-071536"
    "2026-06-24"
    "no DOI"
    "https://www.sec.gov/Archives/edgar/data/2051380/000121390026071536/xslF345X06/ownership.xml"
    beneficialOwnershipChange)
  (secArtifact "0001213900-26-071536"
    "https://www.sec.gov/Archives/edgar/data/2051380/000121390026071536/xslF345X06/ownership.xml")
  "Supports the reported vesting/conversion and beneficial-ownership count only."
  true false false false

ericDominariWarrantExercise : TradeEvidenceClaim
ericDominariWarrantExercise = tradeEvidenceClaim
  "DOMH-2026-05-22-warrant-exercise"
  "Eric Trump"
  "Dominari Holdings Inc."
  warrantExerciseClaim
  "2026-05-22"
  "2026-06-01"
  "SEC Schedule 13G reports exercise of 216,138 Series B warrants into common stock on May 22, 2026 and reported beneficial ownership of 1,182,276 shares, approximately 5.23% of the class as calculated in the filing."
  directDocumentarySupport
  (sourceCitation
    "U.S. Securities and Exchange Commission"
    "Schedule 13G — Eric Trump / Dominari Holdings Inc., accession 0001213900-26-063163"
    "2026-06-01"
    "no DOI"
    "https://www.sec.gov/Archives/edgar/data/12239/000121390026063163/xslSCHEDULE_13G_X02/primary_doc.xml"
    ownershipSchedule)
  (secArtifact "0001213900-26-063163"
    "https://www.sec.gov/Archives/edgar/data/12239/000121390026063163/xslSCHEDULE_13G_X02/primary_doc.xml")
  "Supports the warrant exercise and beneficial-ownership quantities reported in the Schedule 13G only."
  true false false false

trump2026AnnualDisclosure : TradeEvidenceClaim
trump2026AnnualDisclosure = tradeEvidenceClaim
  "Trump-2026-annual-disclosure-availability"
  "Donald J. Trump"
  "2026 certified annual public financial disclosure"
  financialDisclosureClaim
  "2025 reporting period"
  "2026-06-30"
  "The U.S. Office of Government Ethics states that President Trump's certified annual financial disclosure report was made available on June 30, 2026."
  directDocumentarySupport
  (sourceCitation
    "U.S. Office of Government Ethics"
    "Now Available: The President's and Vice President's certified annual financial disclosure reports"
    "2026-06-30"
    "no DOI"
    "https://www2.oge.gov/web/oge.nsf/Resources/Now%2BAvailable%3A%2BThe%2BPresident%E2%80%99s%2Band%2BVice%2BPresident%E2%80%99s%2Bcertified%2Bannual%2Bfinancial%2Bdisclosure%2Breports"
    annualFinancialDisclosure)
  ogeArtifact
  "Supports existence/certification/availability of the annual disclosure; individual asset or income claims require page-level payment from the report."
  true false false false

truthAPIPrimary : TradeEvidenceClaim
truthAPIPrimary = tradeEvidenceClaim
  "TMTG-Truth-API-2026-07-16"
  "Trump Media & Technology Group Corp."
  "Truth API"
  marketDataProductClaim
  "2026-07-16 announcement; 2026-08-01 planned launch"
  "2026-07-16"
  "TMTG's SEC-filed exhibit states Truth API provides licensed real-time/millisecond access to influential Truth Social accounts, including a design target of high-frequency and algorithmic trading firms, while describing the underlying posts as public information."
  issuerStatementSupport
  (sourceCitation
    "Trump Media & Technology Group Corp.; filed with U.S. Securities and Exchange Commission"
    "Trump Media and Technology Group Launches Truth API, a New Licensed Data Service for Financial Services Partners That Provides the Fastest Access to Truth Social's Most Influential Accounts"
    "2026-07-16"
    "no DOI"
    "https://www.sec.gov/Archives/edgar/data/1849635/000143774926023709/ex_988917.htm"
    companyProductDisclosure)
  (secArtifact "TMTG-2026-Truth-API-exhibit-99.1"
    "https://www.sec.gov/Archives/edgar/data/1849635/000143774926023709/ex_988917.htm")
  "Supports company statements about product design, latency, target customers and public-data status; does not itself establish a securities-law violation or trading profit."
  true false false false

truthAPIRegulatoryConcern : TradeEvidenceClaim
truthAPIRegulatoryConcern = tradeEvidenceClaim
  "Schiff-Warren-Truth-API-2026-07-29"
  "Trump Media & Technology Group Corp. / President Donald Trump"
  "Truth API regulatory concern"
  regulatoryConcernClaim
  "2026-07-29"
  "2026-07-29"
  "Senators Adam Schiff and Elizabeth Warren asked the SEC to investigate whether the Truth API arrangement violates applicable federal securities laws. This is an attributed request for investigation, not an adjudicated finding."
  attributedConcernSupport
  (sourceCitation
    "Office of Senator Adam Schiff; Senators Adam Schiff and Elizabeth Warren"
    "Schiff, Warren Call on SEC to Investigate Trump Media's Plan to Give Wall Street Firms Faster Access to Truth Social Posts"
    "2026-07-29"
    "no DOI"
    "https://www.schiff.senate.gov/news/press-releases/news-schiff-warren-call-on-sec-to-investigate-trump-medias-plan-to-give-wall-street-firms-faster-access-to-truth-social-posts/"
    attributedRegulatoryConcern)
  (Source.sourceArtifact
    "Schiff-Warren-Truth-API-letter-2026-07-29"
    Source.documentaryArtifact
    "https://www.schiff.senate.gov/news/press-releases/news-schiff-warren-call-on-sec-to-investigate-trump-medias-plan-to-give-wall-street-firms-faster-access-to-truth-social-posts/"
    "United States Senate")
  "Supports that named lawmakers requested an SEC investigation and their stated concerns; not that the alleged legal violation occurred."
  true false false false

trumpCryptoToTraditionalAssetsReuters : TradeEvidenceClaim
trumpCryptoToTraditionalAssetsReuters = tradeEvidenceClaim
  "Reuters-Trump-crypto-gains-assets-2026-07-13"
  "Donald J. Trump"
  "2026 financial disclosure synthesis"
  financialDisclosureClaim
  "2025 reporting period"
  "2026-07-13"
  "Reuters reports, based on the 2026 financial disclosures, that Trump invested substantial crypto-related gains into stocks and bonds while retaining crypto-related holdings. This is retained as an independent secondary synthesis pending page-level extraction of each underlying disclosure item."
  independentSynthesisSupport
  (sourceCitation
    "Reuters"
    "Trump invested crypto gains in stocks and bonds, filings show"
    "2026-07-13"
    "no DOI"
    "https://www.reuters.com/legal/government/trump-invested-crypto-gains-stocks-bonds-filings-show-2026-07-13/"
    independentReporting)
  (Source.sourceArtifact
    "Reuters-2026-07-13-Trump-disclosure-synthesis"
    Source.derivedArtifact
    "https://www.reuters.com/legal/government/trump-invested-crypto-gains-stocks-bonds-filings-show-2026-07-13/"
    "Reuters")
  "Independent synthesis of filed disclosures; exact component amounts remain source-debt until bound to the underlying annual-disclosure pages."
  false true false false

------------------------------------------------------------------------
-- Hard attribution/promotion boundaries.
------------------------------------------------------------------------

data FilingAutomaticallyProvesInsiderTrading : Set where
data FamilyRelationAutomaticallySharesKnowledge : Set where
data TimingAlignmentAutomaticallyProvesCausation : Set where
data RegulatoryConcernAutomaticallyProvesViolation : Set where
data PaidLowLatencyPublicDataAutomaticallyMeansMNPI : Set where
data FinancialInterestAutomaticallyAuthorisesTrade : Set where

filingDoesNotProveInsiderTrading : FilingAutomaticallyProvesInsiderTrading → ⊥
filingDoesNotProveInsiderTrading ()

familyRelationDoesNotTransportKnowledge : FamilyRelationAutomaticallySharesKnowledge → ⊥
familyRelationDoesNotTransportKnowledge ()

timingDoesNotProveCausation : TimingAlignmentAutomaticallyProvesCausation → ⊥
timingDoesNotProveCausation ()

concernDoesNotProveViolation : RegulatoryConcernAutomaticallyProvesViolation → ⊥
concernDoesNotProveViolation ()

lowLatencyPublicDataDoesNotBecomeMNPI : PaidLowLatencyPublicDataAutomaticallyMeansMNPI → ⊥
lowLatencyPublicDataDoesNotBecomeMNPI ()

financialInterestDoesNotAuthoriseTrade : FinancialInterestAutomaticallyAuthorisesTrade → ⊥
financialInterestDoesNotAuthoriseTrade ()

record TrumpFamilyTradeSourceBoundary : Set where
  constructor trump-family-trade-source-boundary
  field
    transactionAndOwnershipAreSeparateClaims : Bool
    issuerStatementAndIndependentCorroborationAreSeparate : Bool
    attributedInvestigationRequestIsNotAdjudication : Bool
    filingDoesNotProveInsiderTrading : Bool
    familyRelationDoesNotTransportKnowledge : Bool
    timingDoesNotProveCausation : Bool
    lowLatencyPublicDataDoesNotAutomaticallyMeanMNPI : Bool
    annualDisclosureNeedsPageLevelPaymentForComponentClaims : Bool

canonicalTrumpFamilyTradeSourceBoundary : TrumpFamilyTradeSourceBoundary
canonicalTrumpFamilyTradeSourceBoundary =
  trump-family-trade-source-boundary true true true true true true true true
