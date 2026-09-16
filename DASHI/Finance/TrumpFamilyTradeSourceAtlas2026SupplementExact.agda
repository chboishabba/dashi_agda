module DASHI.Finance.TrumpFamilyTradeSourceAtlas2026SupplementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- 2026 SOURCE-ACQUISITION SUPPLEMENT
--
-- Pays additional transaction/ownership propositions not already represented
-- by the existing source stack. Primary SEC/OGE documentary records remain
-- separate from independent Reuters synthesis. None of the records below
-- establishes hidden knowledge, illegality, policy causation, motive, or a
-- dashiTRADE execution signal.
------------------------------------------------------------------------

ericABTCTrustPurchase : Atlas.TradeEvidenceClaim
ericABTCTrustPurchase = Atlas.tradeEvidenceClaim
  "ABTC-2025-12-18-Eric-Trump-trust-purchase"
  "Eric Trump / Eric F. Trump Revocable Trust - 2015"
  "American Bitcoin Corp. (ABTC)"
  Atlas.ownershipClaim
  "2025-12-18"
  "2025-12-22"
  "SEC Schedule 13D Amendment No. 2 states that the Eric F. Trump Revocable Trust - 2015 purchased 285,000 Class A shares on December 18, 2025 at $1.7546 per share using cash on hand; it separately states that Eric Trump, as trustee, may be deemed to beneficially own shares held by the trust."
  Atlas.directDocumentarySupport
  (Atlas.sourceCitation
    "U.S. Securities and Exchange Commission; Eric Trump and Eric F. Trump Revocable Trust - 2015"
    "Schedule 13D Amendment No. 2 — American Bitcoin Corp."
    "2025-12-22"
    "no DOI"
    "https://www.sec.gov/Archives/edgar/data/1755953/000121390025124157/xslSCHEDULE_13D_X01/primary_doc.xml"
    Atlas.ownershipSchedule)
  (Atlas.secArtifact
    "0001213900-25-124157"
    "https://www.sec.gov/Archives/edgar/data/1755953/000121390025124157/xslSCHEDULE_13D_X01/primary_doc.xml")
  "Supports transaction date, quantity, price, source-of-funds statement, trustee relation and beneficial-ownership treatment in the filing only."
  true false false false

trumpOGE278TNvidiaSale : Atlas.TradeEvidenceClaim
trumpOGE278TNvidiaSale = Atlas.tradeEvidenceClaim
  "Trump-2026-OGE-278T-NVDA-sale-2026-03-06"
  "Donald J. Trump"
  "NVIDIA Corp. common stock"
  Atlas.financialDisclosureClaim
  "2026-03-06"
  "2026-05-08"
  "A public OGE Form 278-T filed by Donald J. Trump lists a sale of NVIDIA Corp. common stock on March 6, 2026 in the $250,001-$500,000 reporting range."
  Atlas.directDocumentarySupport
  (Atlas.sourceCitation
    "Donald J. Trump / U.S. Office of Government Ethics"
    "OGE Form 278-T — Periodic Transaction Report, public filing dated May 8, 2026"
    "2026-05-08"
    "no DOI"
    "https://extapps2.oge.gov/201/Presiden.nsf/PAS%2BIndex/405E4EC4E27BE8D185258DF7002DD1C0/%24FILE/Trump%2C%20Donald%20J.-05.08.2026-278T%282%29.pdf"
    Atlas.annualFinancialDisclosure)
  (Source.sourceArtifact
    "Trump-2026-05-08-278T"
    Source.documentaryArtifact
    "https://extapps2.oge.gov/201/Presiden.nsf/PAS%2BIndex/405E4EC4E27BE8D185258DF7002DD1C0/%24FILE/Trump%2C%20Donald%20J.-05.08.2026-278T%282%29.pdf"
    "U.S. Office of Government Ethics")
  "Supports the disclosed sale, date and statutory value range only; not beneficial purpose, broker discretion, market impact, hidden information or motive."
  true false false false

trumpOGE278TAmazonMarchSale : Atlas.TradeEvidenceClaim
trumpOGE278TAmazonMarchSale = Atlas.tradeEvidenceClaim
  "Trump-2026-OGE-278T-AMZN-sale-2026-03-27"
  "Donald J. Trump"
  "Amazon.com Inc. common stock"
  Atlas.financialDisclosureClaim
  "2026-03-27"
  "2026-05-08"
  "The same public OGE Form 278-T lists a sale of Amazon.com Inc. common stock on March 27, 2026 in the $250,001-$500,000 reporting range; this is a distinct row from the separately formalised February 10 Amazon sale."
  Atlas.directDocumentarySupport
  (Atlas.sourceCitation
    "Donald J. Trump / U.S. Office of Government Ethics"
    "OGE Form 278-T — Periodic Transaction Report, public filing dated May 8, 2026"
    "2026-05-08"
    "no DOI"
    "https://extapps2.oge.gov/201/Presiden.nsf/PAS%2BIndex/405E4EC4E27BE8D185258DF7002DD1C0/%24FILE/Trump%2C%20Donald%20J.-05.08.2026-278T%282%29.pdf"
    Atlas.annualFinancialDisclosure)
  (Source.sourceArtifact
    "Trump-2026-05-08-278T"
    Source.documentaryArtifact
    "https://extapps2.oge.gov/201/Presiden.nsf/PAS%2BIndex/405E4EC4E27BE8D185258DF7002DD1C0/%24FILE/Trump%2C%20Donald%20J.-05.08.2026-278T%282%29.pdf"
    "U.S. Office of Government Ethics")
  "Supports the disclosed sale, date and statutory value range only; does not merge this row with another Amazon transaction or infer common strategy."
  true false false false

trumpSpaceXReutersSecondary : Atlas.TradeEvidenceClaim
trumpSpaceXReutersSecondary = Atlas.tradeEvidenceClaim
  "Reuters-Trump-SpaceX-purchase-2026-08-24"
  "Donald J. Trump"
  "SpaceX"
  Atlas.financialDisclosureClaim
  "2026-06-23 transaction reported by Reuters"
  "2026-08-24"
  "Reuters reports that a public financial disclosure showed Donald Trump purchased up to $50,000 of SpaceX shares on June 23, 2026. This atlas retains the report as independent secondary synthesis until the exact underlying transaction-report row is bound directly."
  Atlas.independentSynthesisSupport
  (Atlas.sourceCitation
    "Reuters"
    "Trump bought shares in Elon Musk's SpaceX in June, financial disclosure shows"
    "2026-08-24"
    "no DOI"
    "https://www.reuters.com/legal/government/trump-bought-shares-elon-musks-spacex-june-financial-disclosure-shows-2026-08-24/"
    Atlas.independentReporting)
  (Source.sourceArtifact
    "Reuters-2026-08-24-Trump-SpaceX"
    Source.derivedArtifact
    "https://www.reuters.com/legal/government/trump-bought-shares-elon-musks-spacex-june-financial-disclosure-shows-2026-08-24/"
    "Reuters")
  "Independent secondary report; exact primary disclosure row remains acquisition debt."
  false true false false

sameFilerDoesNotCollapseTransactionIdentity :
  Atlas.claimId trumpOGE278TNvidiaSale
  ≡ Atlas.claimId trumpOGE278TAmazonMarchSale → ⊥
sameFilerDoesNotCollapseTransactionIdentity ()

record TrumpFamilyTrade2026SupplementBoundary : Set where
  constructor trump-family-trade-2026-supplement-boundary
  field
    trustPurchaseAndBeneficialOwnershipAreDistinctPropositions : Bool
    individual278TRowsRemainDistinctEvents : Bool
    statutoryValueRangeIsNotExactTradePrice : Bool
    secondarySpaceXReportRetainsPrimarySourceDebt : Bool
    transactionTimingDoesNotProveHiddenKnowledge : Bool
    documentaryTradeRecordDoesNotAuthoriseTrade : Bool

canonicalTrumpFamilyTrade2026SupplementBoundary :
  TrumpFamilyTrade2026SupplementBoundary
canonicalTrumpFamilyTrade2026SupplementBoundary =
  trump-family-trade-2026-supplement-boundary true true true true true true
