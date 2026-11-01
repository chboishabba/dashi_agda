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
-- Claim-level documentary layer only. Transaction/ownership records, company
-- product disclosures, annual financial disclosure and attributed regulatory
-- concerns remain separate. None of these source edges by itself proves
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
  trustOwnershipClaim : TradeClaimKind
  filingComplianceClaim : TradeClaimKind
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
    "https://oge.box.com/shared/static/zycb5i2ny8kssm51uzqm8ygyq2zkpkqq.pdf"
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
  "SEC Form 4 reports acquisition of 23,600 restricted stock units at reported price $0; reporting person is identified as director and 10% owner. The form separately reports 114,750,000 shares held indirectly through the Donald J. Trump Revocable Trust."
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
  "Supports the reported RSU acquisition, ownership counts, trust relation and relationship-to-issuer fields only."
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

donJrDominariWarrantExercise : TradeEvidenceClaim
donJrDominariWarrantExercise = tradeEvidenceClaim
  "DOMH-2026-05-22-warrant-exercise"
  "Donald J. Trump Jr."
  "Dominari Holdings Inc."
  warrantExerciseClaim
  "2026-05-22"
  "2026-06-01"
  "SEC Schedule 13G reports Donald J. Trump Jr. acquired 216,138 shares upon exercise of 216,138 Series B warrants on May 22, 2026 and reports 1,182,276 shares beneficially owned, approximately 5.23% of the class under the filing's denominator."
  directDocumentarySupport
  (sourceCitation
    "U.S. Securities and Exchange Commission"
    "Schedule 13G — Donald J. Trump Jr. / Dominari Holdings Inc., accession 0001213900-26-063164"
    "2026-06-01"
    "no DOI"
    "https://www.sec.gov/Archives/edgar/data/12239/000121390026063164/xslSCHEDULE_13G_X02/primary_doc.xml"
    ownershipSchedule)
  (secArtifact "0001213900-26-063164"
    "https://www.sec.gov/Archives/edgar/data/12239/000121390026063164/xslSCHEDULE_13G_X02/primary_doc.xml")
  "Supports the named reporting person, warrant exercise and beneficial-ownership quantities in the Schedule 13G only."
  true false false false

ericAmericanBitcoinOwnership : TradeEvidenceClaim
ericAmericanBitcoinOwnership = tradeEvidenceClaim
  "ABTC-2026-proxy-Eric-Trump-ownership"
  "Eric Trump"
  "American Bitcoin Corp. (ABTC)"
  ownershipClaim
  "2026-04-10 ownership snapshot"
  "2026-04-24"
  "American Bitcoin Corp.'s 2026 proxy statement reports Eric Trump with 68,147,664 Class B shares, corresponding to 9.3% beneficial ownership/voting power under the proxy's stated calculation; this is an ownership snapshot, not a transaction inference."
  directDocumentarySupport
  (sourceCitation
    "American Bitcoin Corp.; filed with U.S. Securities and Exchange Commission"
    "DEF 14A — 2026 proxy statement, beneficial ownership table"
    "2026-04-24"
    "no DOI"
    "https://www.sec.gov/Archives/edgar/data/1755953/000119312526178754/abtc-20260424.htm"
    ownershipSchedule)
  (secArtifact "ABTC-2026-DEF14A"
    "https://www.sec.gov/Archives/edgar/data/1755953/000119312526178754/abtc-20260424.htm")
  "Supports the issuer-reported beneficial-ownership snapshot only; does not establish acquisition timing, profit, policy influence or nonpublic-information use."
  true false false false

trump2026AnnualDisclosure : TradeEvidenceClaim
trump2026AnnualDisclosure = tradeEvidenceClaim
  "Trump-2026-annual-disclosure-availability"
  "Donald J. Trump"
  "2026 certified annual public financial disclosure"
  financialDisclosureClaim
  "2025 reporting period"
  "2026-06-30"
  "The U.S. Office of Government Ethics made President Trump's certified annual financial disclosure report available on June 30, 2026."
  directDocumentarySupport
  (sourceCitation
    "U.S. Office of Government Ethics"
    "President Donald J. Trump — Executive Branch Personnel Public Financial Disclosure Report (OGE Form 278e), annual report for 2025"
    "2026-06-30"
    "no DOI"
    "https://oge.box.com/shared/static/zycb5i2ny8kssm51uzqm8ygyq2zkpkqq.pdf"
    annualFinancialDisclosure)
  ogeArtifact
  "Supports existence/certification/availability of the annual disclosure; component claims are paid separately below."
  true false false false

trumpTMTGTrustDisclosure : TradeEvidenceClaim
trumpTMTGTrustDisclosure = tradeEvidenceClaim
  "Trump-2026-OGE-TMTG-trust"
  "Donald J. Trump"
  "Trump Media & Technology Group Corp. / Donald J. Trump Revocable Trust"
  trustOwnershipClaim
  "2024-12-17 transfer described in 2026 annual report"
  "2026-06-30"
  "Donald Trump's certified annual financial disclosure states that on December 17, 2024 he transferred all 114,750,000 TMTG shares to the Donald J. Trump Revocable Trust, of which he is presently sole beneficiary, and states that the transfer did not involve a purchase or sale."
  directDocumentarySupport
  (sourceCitation
    "Donald J. Trump; certified by U.S. Office of Government Ethics"
    "Executive Branch Personnel Public Financial Disclosure Report (OGE Form 278e), Part 3, TMTG arrangement"
    "2026-06-30"
    "no DOI"
    "https://oge.box.com/shared/static/zycb5i2ny8kssm51uzqm8ygyq2zkpkqq.pdf"
    annualFinancialDisclosure)
  ogeArtifact
  "Supports the filer-declared trust transfer, beneficiary status and no-purchase/no-sale characterization in Part 3 of the certified disclosure."
  true false false false

trumpLateTransactionReportingFees : TradeEvidenceClaim
trumpLateTransactionReportingFees = tradeEvidenceClaim
  "Trump-2026-OGE-late-278T-fees"
  "Donald J. Trump"
  "OGE periodic transaction reporting"
  filingComplianceClaim
  "transactions preceding annual filing"
  "2026-06-30"
  "The reviewing-official comments on the certified 2026 annual disclosure state that the filer paid late filing fees related to transactions not previously reported on OGE Form 278-Ts."
  directDocumentarySupport
  (sourceCitation
    "U.S. Office of Government Ethics / reviewing official comment"
    "Executive Branch Personnel Public Financial Disclosure Report (OGE Form 278e), filer-information page"
    "2026-06-30"
    "no DOI"
    "https://oge.box.com/shared/static/zycb5i2ny8kssm51uzqm8ygyq2zkpkqq.pdf"
    annualFinancialDisclosure)
  ogeArtifact
  "Supports only the reviewing-official statement that late filing fees were paid for transactions not previously reported on 278-Ts; it does not by itself establish motive, concealment or any separate criminal/civil violation."
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
  "Reuters reports, based on the 2026 financial disclosures, that Trump invested substantial crypto-related gains into stocks and bonds while retaining crypto-related holdings. This is retained as an independent secondary synthesis; exact component amounts require individual line-item binding to the disclosure."
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
  "Independent synthesis of filed disclosures; exact component amounts remain source-debt until bound to the underlying annual-disclosure lines/pages."
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
data LateFeeAutomaticallyMeansConcealment : Set where

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

lateFeeDoesNotProveConcealment : LateFeeAutomaticallyMeansConcealment → ⊥
lateFeeDoesNotProveConcealment ()

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
    annualDisclosureComponentClaimsRequirePageLevelPayment : Bool
    lateFilingFeeDoesNotAutomaticallyMeanConcealment : Bool

canonicalTrumpFamilyTradeSourceBoundary : TrumpFamilyTradeSourceBoundary
canonicalTrumpFamilyTradeSourceBoundary =
  trump-family-trade-source-boundary true true true true true true true true true
