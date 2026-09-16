module DASHI.Finance.TruthAPIExecutiveStatementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- ATTRIBUTED EXECUTIVE STATEMENT LAYER
--
-- An SEC-filed Financial Times interview quotes TMTG interim CEO Kevin McGurn
-- describing about ten signed groups, mostly high-frequency traders, at roughly
-- $60,000-$100,000 per month.  This is primary evidence that the named executive
-- made those statements (within the filed article), not executed-contract proof
-- for any customer and not a regulator/court finding.
------------------------------------------------------------------------

secFiledInterviewArtifact : Source.SourceArtifact
secFiledInterviewArtifact =
  Source.sourceArtifact
    "TMTG-2026-FT-McGurn-interview-filed-exhibit"
    Source.documentaryArtifact
    "https://www.sec.gov/Archives/edgar/data/1849635/000143774926026809/ex_1002711.htm"
    "Trump Media & Technology Group SEC-filed exhibit reproducing Financial Times interview"

truthAPIExecutiveCustomerClassStatement : Atlas.TradeEvidenceClaim
truthAPIExecutiveCustomerClassStatement =
  Atlas.tradeEvidenceClaim
    "TMTG-McGurn-Truth-API-customer-class-2026"
    "Kevin McGurn, interim CEO of Trump Media & Technology Group Corp."
    "Truth API customer class"
    Atlas.marketDataProductClaim
    "statement published/filed August 2026"
    "2026-08"
    "An SEC-filed Financial Times interview attributes to Kevin McGurn the statement that about ten groups had signed Truth API deals and that they were mostly high-frequency traders. This pays the attributed executive statement only; it does not identify the customers or prove the statement independently."
    Atlas.issuerStatementSupport
    (Atlas.sourceCitation
      "Daniel Thomas, Financial Times; statements attributed to Kevin McGurn; exhibit filed by Trump Media & Technology Group Corp."
      "Kevin McGurn, the executive turning Trump's posts into a media empire — SEC-filed exhibit"
      "2026-08"
      "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1849635/000143774926026809/ex_1002711.htm"
      Atlas.companyProductDisclosure)
    secFiledInterviewArtifact
    "Supports only that the filed interview attributes the customer-count/class statement to McGurn. Customer identities and executed contract records remain unpaid."
    true false false false

truthAPIExecutivePriceBandStatement : Atlas.TradeEvidenceClaim
truthAPIExecutivePriceBandStatement =
  Atlas.tradeEvidenceClaim
    "TMTG-McGurn-Truth-API-price-band-2026"
    "Kevin McGurn, interim CEO of Trump Media & Technology Group Corp."
    "Truth API stated monthly pricing"
    Atlas.informationLatencyClaim
    "statement published/filed August 2026"
    "2026-08"
    "The same SEC-filed Financial Times interview attributes to McGurn a stated Truth API rate of $60,000-$100,000 per month. This is an attributed executive pricing statement, not proof of the exact executed price paid by any particular customer."
    Atlas.issuerStatementSupport
    (Atlas.sourceCitation
      "Daniel Thomas, Financial Times; statements attributed to Kevin McGurn; exhibit filed by Trump Media & Technology Group Corp."
      "Kevin McGurn, the executive turning Trump's posts into a media empire — SEC-filed exhibit"
      "2026-08"
      "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1849635/000143774926026809/ex_1002711.htm"
      Atlas.companyProductDisclosure)
    secFiledInterviewArtifact
    "Pays the attributed $60,000-$100,000 monthly price-band statement only; executed customer-specific prices and terms remain unpaid."
    true false false false

------------------------------------------------------------------------
-- Statement / contract boundary.
------------------------------------------------------------------------

data ExecutiveStatementAutomaticallyEqualsExecutedContract : Set where
data ExecutiveCustomerClassStatementIdentifiesCounterparty : Set where
data FiledInterviewAutomaticallyIndependentlyCorroborated : Set where

statementDoesNotEqualExecutedContract :
  ExecutiveStatementAutomaticallyEqualsExecutedContract → ⊥
statementDoesNotEqualExecutedContract ()

customerClassDoesNotIdentifyCounterparty :
  ExecutiveCustomerClassStatementIdentifiesCounterparty → ⊥
customerClassDoesNotIdentifyCounterparty ()

issuerFiledInterviewIsNotIndependentCorroborationByItself :
  FiledInterviewAutomaticallyIndependentlyCorroborated → ⊥
issuerFiledInterviewIsNotIndependentCorroborationByItself ()

record TruthAPIExecutiveStatementBoundary : Set where
  constructor truth-api-executive-statement-boundary
  field
    namedExecutiveStatementPaid : Bool
    approximateCustomerClassStatementPaid : Bool
    attributedPriceBandStatementPaid : Bool
    executedContractStillUnpaid : Bool
    customerIdentityStillUnpaid : Bool
    independentVerificationStillSeparate : Bool

canonicalTruthAPIExecutiveStatementBoundary : TruthAPIExecutiveStatementBoundary
canonicalTruthAPIExecutiveStatementBoundary =
  truth-api-executive-statement-boundary true true true true true true
