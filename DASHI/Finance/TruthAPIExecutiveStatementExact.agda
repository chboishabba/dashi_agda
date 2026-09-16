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
-- SEC-furnished interview material records named statements by TMTG interim CEO
-- Kevin McGurn about customers, pricing, latency, public-information status and
-- the President's management separation.  These are primary evidence that the
-- statements were made, not independent proof that each underlying proposition
-- is true.
------------------------------------------------------------------------

secFiledFTInterviewArtifact : Source.SourceArtifact
secFiledFTInterviewArtifact =
  Source.sourceArtifact
    "TMTG-2026-FT-McGurn-interview-filed-exhibit"
    Source.documentaryArtifact
    "https://www.sec.gov/Archives/edgar/data/1849635/000143774926026809/ex_1002711.htm"
    "Trump Media & Technology Group SEC-filed exhibit reproducing Financial Times interview"

secFurnishedCNBCTranscriptArtifact : Source.SourceArtifact
secFurnishedCNBCTranscriptArtifact =
  Source.sourceArtifact
    "TMTG-2026-08-24-CNBC-McGurn-transcript"
    Source.documentaryArtifact
    "https://www.sec.gov/Archives/edgar/data/1849635/000143774926029174/ex_1008428.htm"
    "Trump Media & Technology Group Form 8-K Regulation FD exhibit — CNBC interview transcript"

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
    secFiledFTInterviewArtifact
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
    secFiledFTInterviewArtifact
    "Pays the attributed $60,000-$100,000 monthly price-band statement only; executed customer-specific prices and terms remain unpaid."
    true false false false

truthAPIExecutiveLatencyDefense : Atlas.TradeEvidenceClaim
truthAPIExecutiveLatencyDefense =
  Atlas.tradeEvidenceClaim
    "TMTG-McGurn-Truth-API-50ms-public-information-defense"
    "Kevin McGurn, interim CEO of Trump Media & Technology Group Corp."
    "Truth API latency/public-information characterization"
    Atlas.informationLatencyClaim
    "CNBC interview 2026-08-24"
    "2026-08-24"
    "In an SEC-furnished CNBC transcript, McGurn states that Truth API gives roughly a 50-millisecond advantage and characterizes the underlying posts as public information available in real time, attributing the latency difference to machine-readable delivery. This is TMTG's executive characterization, not an independent market-structure or legal finding."
    Atlas.issuerStatementSupport
    (Atlas.sourceCitation
      "Kevin McGurn; CNBC Squawk Box transcript furnished by Trump Media & Technology Group Corp."
      "CNBC Interview Transcript — Exhibit 99.1 to TMTG Form 8-K"
      "2026-08-24"
      "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1849635/000143774926029174/ex_1008428.htm"
      Atlas.companyProductDisclosure)
    secFurnishedCNBCTranscriptArtifact
    "Pays the attributed 50-millisecond/public-information defense statement only. It does not adjudicate whether the service creates legally relevant unequal access or measure customer trading advantage."
    true false false false

trumpManagementSeparationExecutiveStatement : Atlas.TradeEvidenceClaim
trumpManagementSeparationExecutiveStatement =
  Atlas.tradeEvidenceClaim
    "TMTG-McGurn-Trump-management-separation-statement"
    "Kevin McGurn, interim CEO of Trump Media & Technology Group Corp."
    "Donald J. Trump's operational-management / company-information relationship"
    Atlas.financialDisclosureClaim
    "statement published/filed August 2026"
    "2026-08"
    "The SEC-filed Financial Times interview attributes to McGurn the statement that President Trump has no management role at TMTG and learns of company developments when they are publicly announced, like other shareholders. This is a named executive statement and potential counterevidence leaf; it is not independent proof about all communications or information flows."
    Atlas.issuerStatementSupport
    (Atlas.sourceCitation
      "Daniel Thomas, Financial Times; statements attributed to Kevin McGurn; exhibit filed by Trump Media & Technology Group Corp."
      "Kevin McGurn, the executive turning Trump's posts into a media empire — SEC-filed exhibit"
      "2026-08"
      "no DOI"
      "https://www.sec.gov/Archives/edgar/data/1849635/000143774926026809/ex_1002711.htm"
      Atlas.companyProductDisclosure)
    secFiledFTInterviewArtifact
    "Pays only the attributed executive statement about management role/information timing; it does not establish a universal absence of private communication, nor does it prove or disprove any legal theory."
    true false false false

------------------------------------------------------------------------
-- Statement / contract / fact boundary.
------------------------------------------------------------------------

data ExecutiveStatementAutomaticallyEqualsExecutedContract : Set where
data ExecutiveCustomerClassStatementIdentifiesCounterparty : Set where
data FiledInterviewAutomaticallyIndependentlyCorroborated : Set where
data ExecutivePublicInformationCharacterizationAutomaticallySettlesLaw : Set where
data ExecutiveNoManagementStatementAutomaticallyProvesNoPrivateCommunication : Set where

statementDoesNotEqualExecutedContract :
  ExecutiveStatementAutomaticallyEqualsExecutedContract → ⊥
statementDoesNotEqualExecutedContract ()

customerClassDoesNotIdentifyCounterparty :
  ExecutiveCustomerClassStatementIdentifiesCounterparty → ⊥
customerClassDoesNotIdentifyCounterparty ()

issuerFiledInterviewIsNotIndependentCorroborationByItself :
  FiledInterviewAutomaticallyIndependentlyCorroborated → ⊥
issuerFiledInterviewIsNotIndependentCorroborationByItself ()

publicInformationDefenseDoesNotSettleLaw :
  ExecutivePublicInformationCharacterizationAutomaticallySettlesLaw → ⊥
publicInformationDefenseDoesNotSettleLaw ()

managementSeparationStatementDoesNotProveNoPrivateCommunication :
  ExecutiveNoManagementStatementAutomaticallyProvesNoPrivateCommunication → ⊥
managementSeparationStatementDoesNotProveNoPrivateCommunication ()

record TruthAPIExecutiveStatementBoundary : Set where
  constructor truth-api-executive-statement-boundary
  field
    namedExecutiveStatementPaid : Bool
    approximateCustomerClassStatementPaid : Bool
    attributedPriceBandStatementPaid : Bool
    attributedLatencyDefensePaid : Bool
    attributedManagementSeparationStatementPaid : Bool
    executedContractStillUnpaid : Bool
    customerIdentityStillUnpaid : Bool
    independentVerificationStillSeparate : Bool
    legalMeritsStillSeparate : Bool

canonicalTruthAPIExecutiveStatementBoundary : TruthAPIExecutiveStatementBoundary
canonicalTruthAPIExecutiveStatementBoundary =
  truth-api-executive-statement-boundary
    true true true true true true true true true
