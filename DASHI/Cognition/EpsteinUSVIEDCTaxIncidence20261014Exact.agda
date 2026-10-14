module DASHI.Cognition.EpsteinUSVIEDCTaxIncidence20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- USVI ECONOMIC DEVELOPMENT COMMISSION TAX-INCIDENCE LAYER
--
-- Source spine: court-filed JPMorgan expert exhibits and related USVI/JPMorgan
-- litigation material. Tax benefits are treated as public-policy incidence:
-- retained private capital versus foregone public revenue, not as automatic
-- proof of bribery, fraud, or personal responsibility by every official who
-- served during the programme period.
------------------------------------------------------------------------

data TaxEntity : Set where
  financialTrust : TaxEntity
  southernTrust : TaxEntity

record TaxBenefitReceipt : Set where
  constructor tax-benefit-receipt
  field
    entity : TaxEntity
    period : String
    benefitUSD : Nat
    source : String
    courtFiledEstimate : Bool
    wrongdoingEstablishedByThisReceipt : Bool
open TaxBenefitReceipt public

financialTrustEDCBenefit : TaxBenefitReceipt
financialTrustEDCBenefit = tax-benefit-receipt
  financialTrust "1999-2012" 219835233
  "USVI v JPMorgan court exhibits / JPMorgan EDC analysis"
  true false

southernTrustEDCBenefit : TaxBenefitReceipt
southernTrustEDCBenefit = tax-benefit-receipt
  southernTrust "2013-2018" 80576235
  "USVI v JPMorgan court exhibits / JPMorgan EDC analysis"
  true false

record TaxPaymentReceipt : Set where
  constructor tax-payment-receipt
  field
    entity : TaxEntity
    period : String
    incomeTaxPaidUSD : Nat
    source : String
open TaxPaymentReceipt public

financialTrustIncomeTaxPaid : TaxPaymentReceipt
financialTrustIncomeTaxPaid = tax-payment-receipt
  financialTrust "1999-2012" 27282065
  "USVI v JPMorgan Document 290-07, Exhibit 1 — Analysis of Economic Development Commission Credits"

record TaxIncidenceBoundary : Set where
  constructor tax-incidence-boundary
  field
    financialTrustBenefitPaid : Bool
    southernTrustBenefitPaid : Bool
    combinedBenefitApproximately300m : Bool
    financialTrustIncomeTaxPaymentPaid : Bool
    taxBenefitIncreasesRetainedCapitalRelativeToNoBenefit : Bool
    taxBenefitImpliesImproperOfficialAct : Bool
    temporalOfficialServiceImpliesPersonalResponsibility : Bool
    programmeBenefitImpliesPrivateInvestmentEarmarking : Bool
open TaxIncidenceBoundary public

canonicalTaxIncidenceBoundary : TaxIncidenceBoundary
canonicalTaxIncidenceBoundary = tax-incidence-boundary
  true true true true true false false false

data TaxBenefitImpliesImproperAct : Set where
data OfficialTenureImpliesPersonalResponsibility : Set where
data TaxBenefitImpliesEarmarkedInvestment : Set where

taxBenefitDoesNotCreateImproperAct : TaxBenefitImpliesImproperAct → ⊥
taxBenefitDoesNotCreateImproperAct ()

officialTenureDoesNotCreatePersonalResponsibility : OfficialTenureImpliesPersonalResponsibility → ⊥
officialTenureDoesNotCreatePersonalResponsibility ()

taxBenefitDoesNotCreateEarmarking : TaxBenefitImpliesEarmarkedInvestment → ⊥
taxBenefitDoesNotCreateEarmarking ()

------------------------------------------------------------------------
-- Capital-pool significance.
------------------------------------------------------------------------

record RetainedCapitalEffect : Set where
  constructor retained-capital-effect
  field
    lowerTaxOutflowCanIncreaseDeployableCapital : Bool
    retainedCapitalCanCompoundThroughInvestment : Bool
    exactTaxDollarToExactInvestmentRequiredForCapacityClaim : Bool
    privateBenefitAndPublicRevenueCostShouldBothBeMeasured : Bool
open RetainedCapitalEffect public

canonicalRetainedCapitalEffect : RetainedCapitalEffect
canonicalRetainedCapitalEffect = retained-capital-effect
  true true false true

------------------------------------------------------------------------
-- Remaining max-cut.
------------------------------------------------------------------------

data EDCDebt : Set where
  annualBenefitReconciliation : EDCDebt
  statutoryCertificateTerms : EDCDebt
  complianceReviews : EDCDebt
  employmentAndLocalSpendIncidence : EDCDebt
  effectiveTaxRateReconstruction : EDCDebt
  postSettlementRepaymentIncidence : EDCDebt

record EDCAcquisition : Set where
  constructor edc-acquisition
  field
    debt : EDCDebt
    priority : Nat
    question : String
open EDCAcquisition public

canonicalEDCAcquisition : List EDCAcquisition
canonicalEDCAcquisition =
  edc-acquisition annualBenefitReconciliation 100
    "Reconcile Financial Trust and Southern Trust benefits year-by-year to tax returns, certificates and EDC calculations rather than relying only on aggregate court-exhibit totals."
  ∷ edc-acquisition statutoryCertificateTerms 99
    "Acquire every certificate/extension and exact exemption condition, including employment, local-investment and residency obligations."
  ∷ edc-acquisition complianceReviews 99
    "Resolve annual compliance findings, deficiencies, waivers and corrective actions while keeping institutional approval distinct from substantive truth."
  ∷ edc-acquisition employmentAndLocalSpendIncidence 98
    "Measure actual USVI employment, payroll, charitable/local spending and infrastructure use against foregone revenue to compute public/private incidence."
  ∷ edc-acquisition effectiveTaxRateReconstruction 98
    "Reconstruct ordinary business income, tax paid and effective rates from primary returns/exhibits without mixing investment income, fee income and entity transfers."
  ∷ edc-acquisition postSettlementRepaymentIncidence 97
    "Trace later estate/USVI settlement repayments against historical benefits without treating civil settlement as admission beyond its terms."
  ∷ []
