module DASHI.Finance.TrumpFamilyTradePrimarySourceRound3Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- ROUND-THREE PRIMARY ACQUISITION
--
-- This tranche pays three previously useful-but-coarse coordinates:
--
--   * an exact President-level OGE 278-T transaction event;
--   * Eric Trump's original American Bitcoin Schedule 13D lineage;
--   * Truth API's transition from announced product to actual launch/customer
--     agreements/revenue according to later SEC-filed company disclosures.
--
-- None of these receipts establishes motive, MNPI, insider trading, policy
-- causation, customer identity, realised trading advantage, or a trade signal.
------------------------------------------------------------------------

oge278TArtifact : Source.SourceArtifact
oge278TArtifact =
  Source.sourceArtifact
    "Donald-J-Trump-2026-05-08-278T"
    Source.documentaryArtifact
    "https://extapps2.oge.gov/201/Presiden.nsf/PAS%2BIndex/405E4EC4E27BE8D185258DF7002DD1C0/%24FILE/Trump%2C%20Donald%20J.-05.08.2026-278T%282%29.pdf"
    "U.S. Office of Government Ethics — OGE Form 278-T periodic transaction report"

trumpCoinbaseSale20260212 : Atlas.TradeEvidenceClaim
trumpCoinbaseSale20260212 =
  Atlas.tradeEvidenceClaim
    "OGE-278T-2026-02-12-COIN-sale"
    "Donald J. Trump"
    "Coinbase Global Inc. Class A"
    Atlas.financialDisclosureClaim
    "2026-02-12"
    "2026-05-08 periodic transaction report"
    "President Trump's OGE Form 278-T reports a sale of Coinbase Global Inc. Class A on February 12, 2026 in the $50,001-$100,000 reporting band. The public form records a transaction event and value band; it does not identify the investment decision-maker or source of funds."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "Donald J. Trump, filer; U.S. Office of Government Ethics"
      "OGE Form 278-T — Periodic Transaction Report, Donald J. Trump, report dated May 8, 2026"
      "2026-05-08"
      "no DOI"
      "https://extapps2.oge.gov/201/Presiden.nsf/PAS%2BIndex/405E4EC4E27BE8D185258DF7002DD1C0/%24FILE/Trump%2C%20Donald%20J.-05.08.2026-278T%282%29.pdf"
      Atlas.annualFinancialDisclosure)
    oge278TArtifact
    "Pays the named security, sale direction, transaction date and disclosed value band only. It does not establish who selected the trade, why it was selected, whether crypto-business proceeds funded it, or any policy-information edge."
    true false false false

ericAmericanBitcoinInitial13D : Atlas.TradeEvidenceClaim
ericAmericanBitcoinInitial13D =
  Atlas.tradeEvidenceClaim
    "ABTC-2025-09-03-Eric-Trump-13D"
    "Eric Trump"
    "American Bitcoin Corp. (ABTC)"
    Atlas.ownershipClaim
    "2025-09-03"
    "2025 Schedule 13D"
    "Eric Trump's initial American Bitcoin Schedule 13D reports beneficial ownership of 68,147,664 Class A shares, 7.5% under the filing's stated denominator, and identifies his principal occupation as Executive Vice President at the Trump Organization."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "Eric Trump, reporting person; U.S. Securities and Exchange Commission"
      "Schedule 13D — Eric Trump / American Bitcoin Corp., event date September 3, 2025"
      "2025-09-03"
      "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1755953/000095017025114071/xslSCHEDULE_13D_X01/primary_doc.xml"
      Atlas.ownershipSchedule)
    (Atlas.secArtifact
      "0000950170-25-114071"
      "https://www.sec.gov/Archives/edgar/data/1755953/000095017025114071/xslSCHEDULE_13D_X01/primary_doc.xml")
    "Pays the original beneficial-ownership quantity, percentage and occupation fields in the 13D lineage. It does not prove an open-market purchase, policy influence, family information sharing or realised gain."
    true false false false

truthAPIRealisedLaunchAndCustomers : Atlas.TradeEvidenceClaim
truthAPIRealisedLaunchAndCustomers =
  Atlas.tradeEvidenceClaim
    "TMTG-Truth-API-realised-2026-08-10"
    "Trump Media & Technology Group Corp."
    "Truth API"
    Atlas.marketDataProductClaim
    "2026-08-01 launch; status reported 2026-08-10"
    "2026-08-10"
    "TMTG's SEC-filed second-quarter results state that Truth API launched on August 1, 2026, provided licensed low-latency access to publicly available posts, had onboarded institutional customers before launch, had more than ten customer agreements signed to date, and was already generating revenue."
    Atlas.issuerStatementSupport
    (Atlas.sourceCitation
      "Trump Media & Technology Group Corp.; filed with U.S. Securities and Exchange Commission"
      "Trump Media & Technology Group Reports Second Quarter 2026 Results — Exhibit 99.1"
      "2026-08-10"
      "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1849635/000143774926026797/ex_1001984.htm"
      Atlas.companyProductDisclosure)
    (Atlas.secArtifact
      "TMTG-2026-Q2-Truth-API-exhibit-99.1"
      "https://www.sec.gov/Archives/edgar/data/1849635/000143774926026797/ex_1001984.htm")
    "Pays issuer statements that the product launched, had more than ten signed customer agreements, and was generating revenue. Customer identities, individual contract terms, measured end-to-end latency, trading outcomes and legal conclusions remain unpaid."
    true false false false

truthAPILaunchIn10Q : Atlas.TradeEvidenceClaim
truthAPILaunchIn10Q =
  Atlas.tradeEvidenceClaim
    "TMTG-Truth-API-10Q-launch-2026-Q2"
    "Trump Media & Technology Group Corp."
    "Truth API"
    Atlas.marketDataProductClaim
    "2026-08-01"
    "2026-08-10 Form 10-Q"
    "TMTG's Form 10-Q states that on August 1, 2026 the company launched Truth API as a business-to-business subscription providing licensed, low-latency access to publicly available posts from certain top Truth Social accounts."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "Trump Media & Technology Group Corp.; U.S. Securities and Exchange Commission"
      "Form 10-Q for quarter ended June 30, 2026 — subsequent events / MD&A"
      "2026-08-10"
      "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1849635/000143774926026777/djt20260630_10q.htm"
      Atlas.companyProductDisclosure)
    (Atlas.secArtifact
      "0001437749-26-026777"
      "https://www.sec.gov/Archives/edgar/data/1849635/000143774926026777/djt20260630_10q.htm")
    "Pays actual launch status and the company's public-data/low-latency product description in the filed quarterly report. It does not identify counterparties or prove any customer's strategy or profit."
    true false false false

------------------------------------------------------------------------
-- Attribution boundaries exposed by the new receipts.
------------------------------------------------------------------------

data OGETradeAutomaticallyIdentifiesDecisionMaker : Set where
data OGETradeAutomaticallyIdentifiesFundingSource : Set where
data CryptoBusinessIncomeAutomaticallyFundsSpecificTrade : Set where
data CustomerAgreementCountAutomaticallyIdentifiesCustomers : Set where
data LowLatencyProductAutomaticallyProvesTradingAdvantage : Set where

theFilingDoesNotIdentifyDecisionMaker :
  OGETradeAutomaticallyIdentifiesDecisionMaker → ⊥
theFilingDoesNotIdentifyDecisionMaker ()

theFilingDoesNotIdentifyFundingSource :
  OGETradeAutomaticallyIdentifiesFundingSource → ⊥
theFilingDoesNotIdentifyFundingSource ()

cryptoIncomeDoesNotAutoPayTradeFunding :
  CryptoBusinessIncomeAutomaticallyFundsSpecificTrade → ⊥
cryptoIncomeDoesNotAutoPayTradeFunding ()

agreementCountDoesNotIdentifyCounterparties :
  CustomerAgreementCountAutomaticallyIdentifiesCustomers → ⊥
agreementCountDoesNotIdentifyCounterparties ()

lowLatencyDoesNotAutoProveProfitableAdvantage :
  LowLatencyProductAutomaticallyProvesTradingAdvantage → ⊥
lowLatencyDoesNotAutoProveProfitableAdvantage ()

record TrumpFamilyPrimarySourceRound3Boundary : Set where
  constructor trump-family-primary-source-round3-boundary
  field
    president278TEventNowPaid : Bool
    ericAmericanBitcoinHistoricalLineageNowPaid : Bool
    truthAPILaunchNowPaid : Bool
    truthAPICustomerCountIssuerClaimNowPaid : Bool
    truthAPICustomerIdentityStillUnpaid : Bool
    investmentDecisionMakerStillUnpaid : Bool
    transactionFundingSourceStillUnpaid : Bool
    lowLatencyDoesNotProveProfitableTrading : Bool

canonicalTrumpFamilyPrimarySourceRound3Boundary :
  TrumpFamilyPrimarySourceRound3Boundary
canonicalTrumpFamilyPrimarySourceRound3Boundary =
  trump-family-primary-source-round3-boundary
    true true true true true true true true
