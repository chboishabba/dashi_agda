module DASHI.Finance.OGE278TReportingSemanticsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- OGE FORM 278-T REPORTING SEMANTICS
--
-- OGE's own instructions constrain what can be inferred from a periodic
-- transaction report.  The form covers reportable purchases/sales/exchanges in
-- excess of $1,000 made on behalf of the filer, spouse, or dependent child,
-- subject to enumerated exceptions; it reports amount bands, and imposes a
-- filing deadline tied to notification/transaction date.  Those semantics make
-- the public record a financial-interest transaction ledger, not an automatic
-- record of who personally selected or executed each order.
------------------------------------------------------------------------

oge278TSemanticsArtifact : Source.SourceArtifact
oge278TSemanticsArtifact =
  Source.sourceArtifact
    "OGE-Form-278T-instructions-2024-2026"
    Source.documentaryArtifact
    "https://extapps2.oge.gov/201/presiden.nsf/pas%2Bindex/405e4ec4e27be8d185258df7002dd1c0/%24file/trump%2C%20donald%20j.-05.08.2026-278t%282%29.pdf"
    "U.S. Office of Government Ethics — OGE Form 278-T instructions"

record OGE278TReportingSemantics : Set₁ where
  constructor oge-278t-reporting-semantics
  field
    source : Source.SourceArtifact
    reportableTransactionThresholdReference : String
    coveredPersonsReference : String
    filingTimingReference : String
    amountBandReference : String

    coversFilerSpouseDependentChildTransactions : Bool
    reportsPurchasesSalesExchanges : Bool
    amountsAreReportedInBands : Bool
    personallySelectedByNamedFilerAlwaysProved : Bool
    exactExecutionPriceAlwaysProved : Bool
    exactShareQuantityAlwaysProved : Bool

open OGE278TReportingSemantics public

canonicalOGE278TSemantics : OGE278TReportingSemantics
canonicalOGE278TSemantics =
  oge-278t-reporting-semantics
    oge278TSemanticsArtifact
    "OGE 278-T summary: report covered securities transactions exceeding $1,000, subject to listed exceptions"
    "OGE 278-T summary: transactions may be made on behalf of filer, spouse, or dependent child"
    "OGE 278-T summary: report within 30 days of notification and no later than 45 days after transaction"
    "OGE 278-T transaction table reports categorical dollar ranges rather than exact notionals"
    true true true false false false

------------------------------------------------------------------------
-- Attribution consequences.
------------------------------------------------------------------------

data PTRLineAutomaticallyMeansFilerPersonallyDirected : Set where
data PTRLineAutomaticallyIdentifiesCoveredPerson : Set where
data PTRBandAutomaticallyMeansExactNotional : Set where
data PTRDateAutomaticallyMeansInformationAvailableSameDay : Set where
\data PTRFilingLagAutomaticallyMeansConcealment : Set where

ptrLineDoesNotProvePersonalDirection :
  PTRLineAutomaticallyMeansFilerPersonallyDirected → ⊥
ptrLineDoesNotProvePersonalDirection ()

ptrLineDoesNotAlwaysIdentifyCoveredPerson :
  PTRLineAutomaticallyIdentifiesCoveredPerson → ⊥
ptrLineDoesNotAlwaysIdentifyCoveredPerson ()

ptrBandDoesNotGiveExactNotional :
  PTRBandAutomaticallyMeansExactNotional → ⊥
ptrBandDoesNotGiveExactNotional ()

transactionDateDoesNotEqualPublicInformationDate :
  PTRDateAutomaticallyMeansInformationAvailableSameDay → ⊥
transactionDateDoesNotEqualPublicInformationDate ()

filingLagDoesNotAutomaticallyMeanConcealment :
  PTRFilingLagAutomaticallyMeansConcealment → ⊥
filingLagDoesNotAutomaticallyMeanConcealment ()

------------------------------------------------------------------------
-- Source-bounded claim about the reporting system itself.
------------------------------------------------------------------------

ogePTRSemanticsClaim : Atlas.TradeEvidenceClaim
ogePTRSemanticsClaim =
  Atlas.tradeEvidenceClaim
    "OGE-278T-reporting-semantics"
    "U.S. Office of Government Ethics"
    "Periodic Transaction Report reporting semantics"
    Atlas.financialDisclosureClaim
    "standing form semantics"
    "2026 observation of current OGE guidance/form"
    "OGE Form 278-T is a periodic disclosure mechanism for reportable purchases, sales or exchanges of securities and similar assets made on behalf of covered persons. It reports transaction dates and amount ranges; it does not by itself identify investment rationale or personal order selection."
    Atlas.directDocumentarySupport
    (Atlas.sourceCitation
      "U.S. Office of Government Ethics"
      "OGE Form 278-T — Periodic Transaction Report instructions and public financial disclosure guidance"
      "2026 access"
      "no DOI"
      "https://extapps2.oge.gov/web/OGE.nsf/publicresources_disclosure-faq"
      Atlas.annualFinancialDisclosure)
    oge278TSemanticsArtifact
    "Pays form/reporting semantics only; it is not a finding about any individual transaction's decision-maker or legality."
    true false false false

record OGE278TReportingSemanticsBoundary : Set where
  constructor oge-278t-reporting-semantics-boundary
  field
    transactionExistenceMayBePaidByPTR : Bool
    valueBandMayBePaidByPTR : Bool
    personalDirectionNotAutomatic : Bool
    coveredPersonIdentityNotAlwaysRecoverable : Bool
    exactNotionalNotAutomatic : Bool
    publicInformationTimeDistinctFromTransactionTime : Bool
    filingLagNotAutomaticallyConcealment : Bool

canonicalOGE278TReportingSemanticsBoundary : OGE278TReportingSemanticsBoundary
canonicalOGE278TReportingSemanticsBoundary =
  oge-278t-reporting-semantics-boundary
    true true true true true true true
