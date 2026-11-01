module DASHI.Finance.TrumpPresident278TTechnologyBasketExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SourceConditionedObservationExact as Source
import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- PRESIDENT-LEVEL OGE 278-T TECHNOLOGY / LARGE-CAP BASKET
--
-- President Trump's May 8, 2026 periodic transaction report directly records
-- multiple reported sales on February 10, 2026.  This owner retains the exact
-- disclosed event/date/value-band propositions while refusing to infer a common
-- strategy, investment decision-maker, information set, policy motive or causal
-- relationship from same-day co-occurrence.
------------------------------------------------------------------------

may8PTRArtifact : Source.SourceArtifact
may8PTRArtifact =
  Source.sourceArtifact
    "Trump-Donald-J-2026-05-08-278T"
    Source.documentaryArtifact
    "https://extapps2.oge.gov/201/presiden.nsf/pas%2Bindex/405e4ec4e27be8d185258df7002dd1c0/%24file/trump%2C%20donald%20j.-05.08.2026-278t%282%29.pdf"
    "U.S. Office of Government Ethics — OGE Form 278-T"

ptrCitation : Atlas.SourceCitation
ptrCitation =
  Atlas.sourceCitation
    "Donald J. Trump, filer; U.S. Office of Government Ethics"
    "OGE Form 278-T — Periodic Transaction Report, Donald J. Trump, report dated May 8, 2026"
    "2026-05-08"
    "no DOI"
    "https://extapps2.oge.gov/201/presiden.nsf/pas%2Bindex/405e4ec4e27be8d185258df7002dd1c0/%24file/trump%2C%20donald%20j.-05.08.2026-278t%282%29.pdf"
    Atlas.annualFinancialDisclosure

palantirSale20260210 : Atlas.TradeEvidenceClaim
palantirSale20260210 =
  Atlas.tradeEvidenceClaim
    "OGE-278T-2026-02-10-PLTR-sale"
    "Donald J. Trump"
    "Palantir Technologies Inc. Class A"
    Atlas.financialDisclosureClaim
    "2026-02-10"
    "2026-05-08 periodic transaction report"
    "The May 8, 2026 OGE Form 278-T reports a sale of Palantir Technologies Inc. Class A on February 10, 2026 in the $1,000,001-$5,000,000 reporting band."
    Atlas.directDocumentarySupport
    ptrCitation
    may8PTRArtifact
    "Pays asset identity, sale direction, date and reporting band only."
    true false false false

metaSale20260210 : Atlas.TradeEvidenceClaim
metaSale20260210 =
  Atlas.tradeEvidenceClaim
    "OGE-278T-2026-02-10-META-sale"
    "Donald J. Trump"
    "Meta Platforms, Inc."
    Atlas.financialDisclosureClaim
    "2026-02-10"
    "2026-05-08 periodic transaction report"
    "The May 8, 2026 OGE Form 278-T reports a sale of Meta Platforms, Inc. on February 10, 2026 in the $5,000,001-$25,000,000 reporting band."
    Atlas.directDocumentarySupport
    ptrCitation
    may8PTRArtifact
    "Pays asset identity, sale direction, date and reporting band only."
    true false false false

amazonSale20260210 : Atlas.TradeEvidenceClaim
amazonSale20260210 =
  Atlas.tradeEvidenceClaim
    "OGE-278T-2026-02-10-AMZN-sale"
    "Donald J. Trump"
    "Amazon.com Inc."
    Atlas.financialDisclosureClaim
    "2026-02-10"
    "2026-05-08 periodic transaction report"
    "The May 8, 2026 OGE Form 278-T reports a sale of Amazon.com Inc. on February 10, 2026 in the $5,000,001-$25,000,000 reporting band."
    Atlas.directDocumentarySupport
    ptrCitation
    may8PTRArtifact
    "Pays asset identity, sale direction, date and reporting band only."
    true false false false

microsoftSale20260210 : Atlas.TradeEvidenceClaim
microsoftSale20260210 =
  Atlas.tradeEvidenceClaim
    "OGE-278T-2026-02-10-MSFT-sale"
    "Donald J. Trump"
    "Microsoft Corp."
    Atlas.financialDisclosureClaim
    "2026-02-10"
    "2026-05-08 periodic transaction report"
    "The May 8, 2026 OGE Form 278-T reports a sale of Microsoft Corp. on February 10, 2026 in the $5,000,001-$25,000,000 reporting band."
    Atlas.directDocumentarySupport
    ptrCitation
    may8PTRArtifact
    "Pays asset identity, sale direction, date and reporting band only."
    true false false false

------------------------------------------------------------------------
-- Same-day observation is deliberately weaker than common-strategy identity.
------------------------------------------------------------------------

data SameDateAutomaticallyMeansSingleStrategy : Set where
data SameDateAutomaticallyMeansSameDecisionMaker : Set where
data TechnologyIssuerAutomaticallyMeansTechnologyPolicyTrade : Set where
data LargeValueBandAutomaticallyMeansExactNotional : Set where

data ReportedSaleAutomaticallyMeansPersonallyDirectedOrder : Set where

sameDateDoesNotProveSingleStrategy :
  SameDateAutomaticallyMeansSingleStrategy → ⊥
sameDateDoesNotProveSingleStrategy ()

sameDateDoesNotProveSameDecisionMaker :
  SameDateAutomaticallyMeansSameDecisionMaker → ⊥
sameDateDoesNotProveSameDecisionMaker ()

technologyIssuerDoesNotCreatePolicyTrade :
  TechnologyIssuerAutomaticallyMeansTechnologyPolicyTrade → ⊥
technologyIssuerDoesNotCreatePolicyTrade ()

valueBandIsNotExactNotional :
  LargeValueBandAutomaticallyMeansExactNotional → ⊥
valueBandIsNotExactNotional ()

reportedSaleDoesNotProvePersonalDirection :
  ReportedSaleAutomaticallyMeansPersonallyDirectedOrder → ⊥
reportedSaleDoesNotProvePersonalDirection ()

record President278TTechnologyBasketBoundary : Set where
  constructor president-278t-technology-basket-boundary
  field
    palantirSalePaid : Bool
    metaSalePaid : Bool
    amazonSalePaid : Bool
    microsoftSalePaid : Bool
    sameDayIsObservable : Bool
    commonStrategyUnpaid : Bool
    decisionMakerUnpaid : Bool
    policyMotiveUnpaid : Bool
    exactNotionalUnpaid : Bool

canonicalPresident278TTechnologyBasketBoundary :
  President278TTechnologyBasketBoundary
canonicalPresident278TTechnologyBasketBoundary =
  president-278t-technology-basket-boundary
    true true true true true true true true true
