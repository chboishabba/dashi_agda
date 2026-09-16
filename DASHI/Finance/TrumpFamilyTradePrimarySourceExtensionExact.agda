module DASHI.Finance.TrumpFamilyTradePrimarySourceExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- PRIMARY-SOURCE EXTENSION
--
-- This owner pays source debt discovered after the first atlas pass.  It keeps
-- filing-level propositions narrow enough that later PNF/game/trading consumers
-- need not reconstruct them from secondary summaries.
------------------------------------------------------------------------

ogeAnnualPDF : Source.SourceArtifact
ogeAnnualPDF =
  Source.sourceArtifact
    "Donald-J-Trump-2026-278ANNUAL"
    Source.documentaryArtifact
    "https://oge.box.com/shared/static/zycb5i2ny8kssm51uzqm8ygyq2zkpkqq.pdf"
    "U.S. Office of Government Ethics — certified 2026 annual financial disclosure"

------------------------------------------------------------------------
-- OGE page-level claims.
------------------------------------------------------------------------

trumpTMTGTrustTransferWasNotSale : Atlas.TradeEvidenceClaim
trumpTMTGTrustTransferWasNotSale =
  Atlas.tradeEvidenceClaim
    "OGE-2026-TMTG-trust-transfer-nonsale"
    "Donald J. Trump"
    "114,750,000 shares of Trump Media & Technology Group Corp. common stock"
    Atlas.ownershipClaim
    "2024-12-17"
    "2026-06-29/30"
    "The certified annual disclosure states that all 114,750,000 TMTG shares were transferred to the Donald J. Trump Revocable Trust, of which the filer was presently sole beneficiary, and explicitly states that the transfer did not involve a purchase or sale."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "Donald J. Trump, filer; U.S. Office of Government Ethics"
      "Public Financial Disclosure Report (OGE Form 278e), 2026 annual report — TMTG trust-transfer narrative"
      "OGE received 2026-06-29; reviewing-official comment 2026-06-30"
      "no DOI"
      "https://oge.box.com/shared/static/zycb5i2ny8kssm51uzqm8ygyq2zkpkqq.pdf"
      Atlas.annualFinancialDisclosure)
    ogeAnnualPDF
    "Pays only the trust-transfer, beneficiary and no-purchase/no-sale propositions on the disclosed TMTG narrative; it does not establish control motive or later trading."
    true false false false

trumpTMTGTrustTradingRightsQualified : Atlas.TradeEvidenceClaim
trumpTMTGTrustTradingRightsQualified =
  Atlas.tradeEvidenceClaim
    "OGE-2026-TMTG-trust-qualified-disposition-rights"
    "Donald J. Trump / Donald J. Trump Revocable Trust"
    "TMTG securities"
    Atlas.financialDisclosureClaim
    "reported current arrangement"
    "2026-06-29/30"
    "The certified annual disclosure states that the Trust and TMTG reserve rights, subject to applicable law and contractual restrictions including TMTG's insider-trading policy, to acquire or dispose of TMTG securities through specified transaction channels."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "Donald J. Trump, filer; U.S. Office of Government Ethics"
      "Public Financial Disclosure Report (OGE Form 278e), 2026 annual report — TMTG restrictions and disposition narrative"
      "2026-06-29/30"
      "no DOI"
      "https://oge.box.com/shared/static/zycb5i2ny8kssm51uzqm8ygyq2zkpkqq.pdf"
      Atlas.annualFinancialDisclosure)
    ogeAnnualPDF
    "Supports existence of the disclosed qualified rights and restrictions only; it does not report that a later transaction occurred."
    true false false false

trumpLate278TFees : Atlas.TradeEvidenceClaim
trumpLate278TFees =
  Atlas.tradeEvidenceClaim
    "OGE-2026-late-278T-fees"
    "Donald J. Trump"
    "periodic transaction reporting compliance"
    Atlas.financialDisclosureClaim
    "transactions referenced by reviewing official"
    "2026-06-30"
    "The reviewing official's comments state that the filer paid late filing fees related to transactions not previously reported on OGE Form 278-Ts."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "U.S. Office of Government Ethics reviewing official"
      "Public Financial Disclosure Report (OGE Form 278e), 2026 annual report — reviewing official comments"
      "2026-06-30"
      "no DOI"
      "https://oge.box.com/shared/static/zycb5i2ny8kssm51uzqm8ygyq2zkpkqq.pdf"
      Atlas.annualFinancialDisclosure)
    ogeAnnualPDF
    "Supports the reviewing official's late-fee/nonprevious-reporting statement; it does not by itself identify each transaction, establish intent, or establish an additional legal violation."
    true false false false

trumpPart7Transactions : Atlas.TradeEvidenceClaim
trumpPart7Transactions =
  Atlas.tradeEvidenceClaim
    "OGE-2026-Part7-transaction-history"
    "Donald J. Trump"
    "Part 7 investment-account transactions"
    Atlas.financialDisclosureClaim
    "2025 reporting period"
    "2026-06-29/30"
    "The certified annual disclosure contains a large Part 7 transaction ledger with dated purchases and sales across multiple investment accounts; examples include June 2, July 1 and November 18, 2025 transaction batches."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "Donald J. Trump, filer; U.S. Office of Government Ethics"
      "Public Financial Disclosure Report (OGE Form 278e), 2026 annual report — Part 7 Transactions"
      "2026-06-29/30"
      "no DOI"
      "https://oge.box.com/shared/static/zycb5i2ny8kssm51uzqm8ygyq2zkpkqq.pdf"
      Atlas.annualFinancialDisclosure)
    ogeAnnualPDF
    "Establishes a primary point-in-time transaction ledger suitable for event-level extraction; this aggregate claim does not infer who selected individual trades or why."
    true false false false

trumpWLFEconomicInterest : Atlas.TradeEvidenceClaim
trumpWLFEconomicInterest =
  Atlas.tradeEvidenceClaim
    "OGE-2026-WLF-economic-interest"
    "Donald J. Trump disclosure structure"
    "DT Marks Defi LLC / WLF Holdco LLC / World Liberty Financial"
    Atlas.financialDisclosureClaim
    "2025 reporting period"
    "2026-06-29/30"
    "The certified annual disclosure reports DT Marks Defi LLC as holding a 38.25% ownership interest in WLF Holdco LLC, reports Trump Family Members as holding 30% of DT Marks Defi LLC, and reports token/equity-sale proceeds through that structure."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "Donald J. Trump, filer; U.S. Office of Government Ethics"
      "Public Financial Disclosure Report (OGE Form 278e), 2026 annual report — WLF Holdco / DT Marks Defi entries"
      "2026-06-29/30"
      "no DOI"
      "https://oge.box.com/shared/static/zycb5i2ny8kssm51uzqm8ygyq2zkpkqq.pdf"
      Atlas.annualFinancialDisclosure)
    ogeAnnualPDF
    "Supports the disclosed entity/economic-right structure and reported proceeds only; 'Trump Family Members' is retained exactly as the public form's category and is not entity-resolved here."
    true false false false

trumpWLFCryptoWallets : Atlas.TradeEvidenceClaim
trumpWLFCryptoWallets =
  Atlas.tradeEvidenceClaim
    "OGE-2026-WLF-crypto-wallets"
    "Donald J. Trump disclosure structure"
    "crypto wallets / World Liberty Financial token-sale proceeds"
    Atlas.financialDisclosureClaim
    "2025 reporting period"
    "2026-06-29/30"
    "The certified annual disclosure reports multiple cold-wallet crypto assets, including Ethereum and Bitcoin entries valued in the form's 'Over $50,000,000' band, alongside separately reported proceeds distributed by World Liberty Financial LLC from token sales."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "Donald J. Trump, filer; U.S. Office of Government Ethics"
      "Public Financial Disclosure Report (OGE Form 278e), 2026 annual report — crypto-wallet and World Liberty Financial token-sale entries"
      "2026-06-29/30"
      "no DOI"
      "https://oge.box.com/shared/static/zycb5i2ny8kssm51uzqm8ygyq2zkpkqq.pdf"
      Atlas.annualFinancialDisclosure)
    ogeAnnualPDF
    "Supports the individual disclosed value bands and reported distribution entries; it does not equate wallet value with realised profit or a securities trade."
    true false false false

------------------------------------------------------------------------
-- Eric Trump / American Bitcoin primary ownership evidence.
------------------------------------------------------------------------

ericAmericanBitcoinOwnership : Atlas.TradeEvidenceClaim
ericAmericanBitcoinOwnership =
  Atlas.tradeEvidenceClaim
    "ABTC-Eric-Trump-2025-2026-ownership"
    "Eric Trump"
    "American Bitcoin Corp. (ABTC)"
    Atlas.ownershipClaim
    "2025-09-03 onward; proxy status reported 2026"
    "2026 proxy / current public filing record"
    "American Bitcoin's 2026 proxy statement reports Eric Trump as a 5%-or-greater stockholder based on his Schedule 13D filings, with 68,147,664 shares shown in the proxy table; the Schedule 13D lineage records his beneficial-ownership reporting and later trust transfer."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "American Bitcoin Corp.; U.S. Securities and Exchange Commission"
      "DEF 14A — American Bitcoin Corp. 2026 proxy statement; Schedule 13D lineage for Eric Trump"
      "2026-04"
      "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1755953/000119312526178754/abtc-20260424.htm"
      Atlas.ownershipSchedule)
    (Atlas.secArtifact
      "ABTC-2026-DEF14A-Eric-Trump-ownership"
      "https://www.sec.gov/Archives/edgar/data/1755953/000119312526178754/abtc-20260424.htm")
    "Supports beneficial-ownership reporting and corporate role context only; it does not establish a 2026 open-market purchase or policy-information edge."
    true false false false

------------------------------------------------------------------------
-- Donald Trump Jr. / PSQH August 2026 private-placement source collision.
------------------------------------------------------------------------

donJrPSQHPrivatePlacement : Atlas.TradeEvidenceClaim
donJrPSQHPrivatePlacement =
  Atlas.tradeEvidenceClaim
    "PSQH-2026-08-13-private-placement-participation"
    "Donald J. Trump Jr."
    "PSQ Holdings, Inc. private placement"
    Atlas.ownershipClaim
    "2026-08-13"
    "2026-08-14/18 filings"
    "PSQ Holdings' filed 8-K identifies Donald J. Trump Jr. among director purchasers in an August 13, 2026 private placement at $3.60 per share; his subsequent SEC Form 4 reports an August 13 transaction. Exact personal allocation is a separate Form-4 proposition."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "PSQ Holdings, Inc.; U.S. Securities and Exchange Commission"
      "Form 8-K — Entry into a Material Definitive Agreement, August 13, 2026 private placement"
      "2026-08-14"
      "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1847064/000110465926097142/tm2623216d1_8k.htm"
      Atlas.beneficialOwnershipChange)
    (Atlas.secArtifact
      "PSQH-2026-08-13-private-placement-8K"
      "https://www.sec.gov/Archives/edgar/data/1847064/000110465926097142/tm2623216d1_8k.htm")
    "Supports named participation and the filed deal terms; does not promote the aggregate offering quantity into Donald Jr.'s personal quantity."
    true false false false

record DocumentaryQuantityCollision : Set₁ where
  constructor documentary-quantity-collision
  field
    subject : String
    leftDocument : String
    rightDocument : String
    leftQuantity : Nat
    rightQuantity : Nat
    quantitiesDiffer : leftQuantity ≡ rightQuantity → ⊥
    collisionReference : String

open DocumentaryQuantityCollision public

psqhAggregateShareCountCollision : DocumentaryQuantityCollision
psqhAggregateShareCountCollision =
  documentary-quantity-collision
    "PSQ Holdings August 13, 2026 private placement aggregate share count"
    "SEC-filed 8-K: 361,385 shares"
    "company/Business Wire release: 361,388 shares"
    361385
    361388
    notEqual
    "retain three-share discrepancy as source residual; do not silently normalize"
  where
    notEqual : 361385 ≡ 361388 → ⊥
    notEqual ()

------------------------------------------------------------------------
-- Evidence-quality laws.
------------------------------------------------------------------------

data AggregateDealSizeAutomaticallyEqualsPersonalAllocation : Set where
data OGETransactionLedgerAutomaticallyIdentifiesDecisionMaker : Set where
data BeneficialOwnershipAutomaticallyMeansOpenMarketPurchase : Set where

aggregateDoesNotEqualPersonalAllocation :
  AggregateDealSizeAutomaticallyEqualsPersonalAllocation → ⊥
aggregateDoesNotEqualPersonalAllocation ()

transactionLedgerDoesNotIdentifyDecisionMaker :
  OGETransactionLedgerAutomaticallyIdentifiesDecisionMaker → ⊥
transactionLedgerDoesNotIdentifyDecisionMaker ()

beneficialOwnershipDoesNotMeanOpenMarketPurchase :
  BeneficialOwnershipAutomaticallyMeansOpenMarketPurchase → ⊥
beneficialOwnershipDoesNotMeanOpenMarketPurchase ()

record TrumpFamilyPrimarySourceExtensionBoundary : Set where
  constructor trump-family-primary-source-extension-boundary
  field
    ogePageLevelClaimsNowPaid : Bool
    tmtgTransferTypePreservedAsNonSale : Bool
    wlfEntityChainPreserved : Bool
    lateFeeCommentDoesNotInferIntent : Bool
    americanBitcoinOwnershipDoesNotInferTrade : Bool
    psqhDocumentDiscrepancyRetained : Bool
    aggregatePlacementDoesNotBecomePersonalAllocation : Bool

canonicalTrumpFamilyPrimarySourceExtensionBoundary :
  TrumpFamilyPrimarySourceExtensionBoundary
canonicalTrumpFamilyPrimarySourceExtensionBoundary =
  trump-family-primary-source-extension-boundary true true true true true true true
