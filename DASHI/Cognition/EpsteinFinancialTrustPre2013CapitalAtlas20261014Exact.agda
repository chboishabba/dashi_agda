module DASHI.Cognition.EpsteinFinancialTrustPre2013CapitalAtlas20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinFinancialTrustAnnualStatementSpine20261014Exact as Annual

------------------------------------------------------------------------
-- FINANCIAL TRUST COMPANY PRE-2013 CAPITAL / INVESTMENT ATLAS
--
-- Financial Trust is treated as a mixed financial vehicle: advisory/management
-- income, proprietary investment capital, partnership positions, trading,
-- credit facilities and inter-entity transfers. Managed/client assets, Epstein
-- personal wealth and FTC corporate assets are not collapsed.
------------------------------------------------------------------------

data FTCSurface : Set where
  personalInvestmentVehicle : FTCSurface
  generalPartner : FTCSurface
  limitedPartnerInvestment : FTCSurface
  securitiesTrading : FTCSurface
  repoAndDerivatives : FTCSurface
  partnershipPortfolio : FTCSurface
  creditFacility : FTCSurface
  charitableAssetTransfer : FTCSurface
  advisoryFeeIncome : FTCSurface
  investmentIncome : FTCSurface
  clientAssetManagement : FTCSurface

record FTCReceipt : Set where
  constructor ftc-receipt
  field
    label : String
    source : String
    sourceClass : String
    boundedFinding : String
    surfaces : List FTCSurface
    amountUSD : Nat
    directObjectPaid : Bool
    wrongdoingPaid : Bool
open FTCReceipt public

jpmRelatedAccountReceipt : FTCReceipt
jpmRelatedAccountReceipt = ftc-receipt
  "JPMorgan related-account description"
  "USVI v JPMorgan, Document 174-1 / JPM-SDNYLIT-00269656"
  "bank due-diligence / court exhibit"
  "JPMorgan described Financial Trust Company as Epstein's personal investment/trading vehicle and as general partner of Family Interest LP, for which Leslie Wexner's children's trust was a limited partner. This pays the bank's relationship classification and GP/LP structure as recorded by JPMorgan, not beneficial ownership of the children's trust assets."
  (personalInvestmentVehicle ∷ generalPartner ∷ [])
  0 true false

record FTCAnnualStatement : Set where
  constructor ftc-annual-statement
  field
    year : Nat
    cashUSD : Nat
    investmentsUSD : Nat
    totalAssetsUSD : Nat
    totalLiabilitiesUSD : Nat
    feeIncomeUSD : Nat
    investmentIncomeUSD : Nat
    netIncomeUSD : Nat
    distributionsUSD : Nat
    source : String
    primaryCourtExhibitPaid : Bool
open FTCAnnualStatement public

ftc2003 : FTCAnnualStatement
ftc2003 = ftc-annual-statement
  2003 60042683 335070706 395646418 563395
  58954853 34282912 89951336 0
  "USVI v JPMorgan, Document 268-52 / 194-22, VI-JPM-000013542"
  true

ftc2006 : FTCAnnualStatement
ftc2006 = ftc-annual-statement
  2006 55700201 303000394 487207276 11231303
  65984969 8051002 70744165 70500000
  "USVI v JPMorgan, Document 268-52, VI-JPM-000013514"
  true

balanceSheet2004 : FTCReceipt
balanceSheet2004 = ftc-receipt
  "Financial Trust 2004 balance sheet"
  "EFTA01720157..166"
  "released company accounting record"
  "Financial Trust's 31 Dec 2004 internal cash-basis balance sheet reports approximately USD537.0m total assets and approximately USD202.2m investment in partnerships, alongside cash, reverse-repo, securities and other positions. The separately filed 2004 statement reports approximately USD563.2m total assets; the accounting-view discrepancy is preserved in the annual-spine owner."
  (securitiesTrading ∷ repoAndDerivatives ∷ partnershipPortfolio ∷ [])
  537033867 true false

partnershipPortfolio2004 : FTCReceipt
partnershipPortfolio2004 = ftc-receipt
  "Financial Trust partnership investment book"
  "EFTA01720157..166"
  "released company accounting record"
  "The 2004 partnership schedule includes positions in Highbridge, Bear Stearns High-Grade Structured, AP Technology Partners, Liquid Funding Holdings, Pinehurst Partners and other funds/vehicles, demonstrating a diversified investment book rather than a fee-only shell."
  (partnershipPortfolio ∷ limitedPartnerInvestment ∷ [])
  202189381 true false

zwirnPosition2006 : FTCReceipt
zwirnPosition2006 = ftc-receipt
  "D.B. Zwirn Special Opportunities position"
  "EFTA00286391..397"
  "fund statement / correspondence"
  "Financial Trust contributed USD80m across 2002-2005 to D.B. Zwirn Special Opportunities Fund; a 30 Sep 2006 statement reports investment value of approximately USD127.45m. Correspondence described roughly USD47m in gains. Investment value is not realised cash profit."
  (limitedPartnerInvestment ∷ partnershipPortfolio ∷ [])
  127451286 true false

ylkAppleTransfer2008 : FTCReceipt
ylkAppleTransfer2008 = ftc-receipt
  "Financial Trust Apple-share transfer to YLK"
  "Wexner Foundation independent review / YLK Form 990-PF lineage"
  "independent-review report citing tax filings"
  "Financial Trust transferred 201,939 Apple shares with reported value USD34,280,154 to YLK Charitable Fund in 2008. The Wexner Foundation review says this formed part of repayment of funds Wexner said Epstein had misappropriated; that characterization is attributed to Wexner/review evidence rather than treated here as an adjudicated criminal finding."
  (charitableAssetTransfer ∷ [])
  34280154 true false

ftc2002PrimaryState : FTCReceipt
ftc2002PrimaryState = ftc-receipt
  "2002 primary Financial Trust statement"
  "USVI v JPMorgan Document 194-22 / 268-52, VI-JPM-000013554"
  "primary court-filed company accounting record"
  "The 2002 Financial Trust statement reports USD386,707,529 total assets, USD77,680,429 fee income, USD44,720,327 investment income and USD118,191,544 net income. The annual-spine owner now pays the complete filed statement rather than relying on a secondary paid-in-capital locator."
  (personalInvestmentVehicle ∷ advisoryFeeIncome ∷ investmentIncome ∷ [])
  386707529 true false

record FTCPre2013Boundary : Set where
  constructor ftc-pre2013-boundary
  field
    primaryAnnualSpine1999to2012Paid : Bool
    largeCorporateAssetBasePaid : Bool
    feeAndInvestmentIncomeSeparatelyPaid : Bool
    diversifiedInvestmentBookPaid : Bool
    zwirnLPInvestmentPaid : Bool
    familyInterestGPLPStructureRecordedByJPM : Bool
    wexnerChildrenTrustAssetsEqualEpsteinPersonalAssets : Bool
    investmentValueEqualsRealisedGain : Bool
    companyAssetsEqualEpsteinNetWorth : Bool
    gpStatusEqualsBeneficialOwnershipOfLPAssets : Bool
    wexnerReviewAttributionEqualsAdjudication : Bool
open FTCPre2013Boundary public

canonicalFTCPre2013Boundary : FTCPre2013Boundary
canonicalFTCPre2013Boundary = ftc-pre2013-boundary
  true true true true true true false false false false false

data CompanyAssetsImpliesPersonalNetWorth : Set where
data GPImpliesBeneficialOwnership : Set where
data InvestmentValueImpliesRealisedGain : Set where
data WexnerReviewImpliesAdjudicatedMisappropriation : Set where

companyAssetsDoNotCreatePersonalNetWorth : CompanyAssetsImpliesPersonalNetWorth → ⊥
companyAssetsDoNotCreatePersonalNetWorth ()

gpDoesNotCreateBeneficialOwnership : GPImpliesBeneficialOwnership → ⊥
gpDoesNotCreateBeneficialOwnership ()

investmentValueDoesNotCreateRealisedGain : InvestmentValueImpliesRealisedGain → ⊥
investmentValueDoesNotCreateRealisedGain ()

wexnerReviewDoesNotCreateAdjudication : WexnerReviewImpliesAdjudicatedMisappropriation → ⊥
wexnerReviewDoesNotCreateAdjudication ()

------------------------------------------------------------------------
-- Pre-2013 Pareto frontier after annual-statement closure.
------------------------------------------------------------------------

data FTCPre2013Debt : Set where
  familyInterestPartnershipAgreement : FTCPre2013Debt
  wexnerChildrenTrustCapitalLedger : FTCPre2013Debt
  feeClientAllocation : FTCPre2013Debt
  zwirnRealisedDistributionLedger : FTCPre2013Debt
  shareholderCapitalSource : FTCPre2013Debt
  full2004PortfolioLookThrough : FTCPre2013Debt
  crisisLossDecomposition : FTCPre2013Debt
  interEntityTransferLedger : FTCPre2013Debt

record FTCPre2013Acquisition : Set where
  constructor ftc-pre2013-acquisition
  field
    debt : FTCPre2013Debt
    priority : Nat
    question : String
open FTCPre2013Acquisition public

canonicalFTCPre2013Acquisition : List FTCPre2013Acquisition
canonicalFTCPre2013Acquisition =
  ftc-pre2013-acquisition familyInterestPartnershipAgreement 100
    "Acquire Family Interest LP's partnership agreement, cap table and account statements to resolve FTC GP rights and the Wexner children's trust LP economics."
  ∷ ftc-pre2013-acquisition feeClientAllocation 100
    "Resolve Financial Trust fee/advisory revenue payer-by-payer; the primary 1999-2012 annual spine is now closed, but annual fee totals are not a client ledger."
  ∷ ftc-pre2013-acquisition wexnerChildrenTrustCapitalLedger 99
    "Trace contributions/distributions between the Wexner children's trust, Family Interest LP and Financial Trust with same-object partnership/bank records."
  ∷ ftc-pre2013-acquisition crisisLossDecomposition 99
    "Decompose 2008-2012 negative related-investment results into realised losses, unrealised marks, write-downs and cash-flow effects."
  ∷ ftc-pre2013-acquisition zwirnRealisedDistributionLedger 99
    "Reconstruct Zwirn/Fortress contributions, valuations, redemptions, settlement and realised cash return; do not equate 2006 NAV with realised profit."
  ∷ ftc-pre2013-acquisition shareholderCapitalSource 98
    "Resolve shareholder contributions and equity changes behind the 2002/earlier corporate capital accounts using the primary statement and stockholder records."
  ∷ ftc-pre2013-acquisition full2004PortfolioLookThrough 98
    "Map Financial Trust's 2004 partnership/securities positions to managers, underlying assets, fees and counterparties while distinguishing direct from indirect exposure."
  ∷ ftc-pre2013-acquisition interEntityTransferLedger 97
    "Join Financial Trust, Epstein personal accounts, Family Interest, COUQ/YLK and later Southern Trust transfers without double-counting the same economic capital."
  ∷ []
