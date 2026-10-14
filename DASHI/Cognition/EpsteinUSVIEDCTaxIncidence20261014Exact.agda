module DASHI.Cognition.EpsteinUSVIEDCTaxIncidence20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- USVI ECONOMIC DEVELOPMENT COMMISSION TAX / COMPLIANCE INCIDENCE
--
-- Court-filed EDC/JPMorgan exhibits permit both sides of the policy incidence
-- to be typed: private tax benefit/retained capital and the programme's local
-- investment, employment, procurement and residency conditions. Institutional
-- compliance findings are attributed to the EDC; they are not a God's-eye
-- finding about every underlying fact, and tax benefits do not by themselves
-- establish bribery, fraud or improper official action.
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

------------------------------------------------------------------------
-- Primary EDC compliance reports.
------------------------------------------------------------------------

record EDCComplianceReceipt : Set where
  constructor edc-compliance-receipt
  field
    period : String
    report : String
    capitalExpenditureUSD : Nat
    localCapitalExpenditureUSD : Nat
    goodsServicesUSD : Nat
    localGoodsServicesUSD : Nat
    fullTimeEmployeeRequirement : Nat
    employeeRequirementMet : Bool
    residencyRequirementMet : Bool
    managementTechnicalRequirementMet : Bool
    procurementProcessMet : Bool
    reportingRequirementMet : Bool
    boundedSpecialConditionFinding : String
    institutionalComplianceFindingOnly : Bool
open EDCComplianceReceipt public

compliance1999to2006 : EDCComplianceReceipt
compliance1999to2006 = edc-compliance-receipt
  "1999-2006"
  "USVI EDA/EDC compliance report, USVI v JPMorgan Document 186-39 / 268-59, VI-JPM-000022898.."
  570067 546447 4252064 0 11
  true true true true true
  "EDC report states Special Conditions #1, #2, #3 and #5 were met and #4 was not specifically met. Goods/services local share is stated as 77%; exact dollar local subtotal should be recovered from the detailed schedule rather than rounded from the percentage."
  true

compliance2007to2008 : EDCComplianceReceipt
compliance2007to2008 = edc-compliance-receipt
  "2007-2008"
  "USVI EDA/EDC inactive-beneficiary compliance report, Document 186-34 / 268-54, VI-JPM-000023079.."
  76806 39634 1404021 965657 11
  true true true false true
  "EDC report states Special Conditions one through five were met, but the procurement-process requirement was not complied with during this review period."
  true

record LocalIncidenceSummary : Set where
  constructor local-incidence-summary
  field
    capitalInvestmentThresholdUSD : Nat
    thresholdMetBy1999 : Bool
    capex1999to2006USD : Nat
    capexLocalSharePct : Nat
    goodsServices1999to2006USD : Nat
    goodsServicesLocalSharePct : Nat
    capex2007to2008USD : Nat
    goodsServices2007to2008USD : Nat
    employeeRequirement : Nat
    privateTaxBenefitMuchLargerThanDirectCapex : Bool
    localProcurementOffsetsFullTaxBenefit : Bool
open LocalIncidenceSummary public

canonicalLocalIncidenceSummary : LocalIncidenceSummary
canonicalLocalIncidenceSummary = local-incidence-summary
  300000 true 570067 96 4252064 77 76806 1404021 11 true false

record TaxIncidenceBoundary : Set where
  constructor tax-incidence-boundary
  field
    financialTrustBenefitPaid : Bool
    southernTrustBenefitPaid : Bool
    combinedBenefitApproximately300m : Bool
    financialTrustIncomeTaxPaymentPaid : Bool
    taxBenefitIncreasesRetainedCapitalRelativeToNoBenefit : Bool
    primaryComplianceReportsPaid : Bool
    localInvestmentEmploymentObligationsPaid : Bool
    taxBenefitImpliesImproperOfficialAct : Bool
    temporalOfficialServiceImpliesPersonalResponsibility : Bool
    programmeBenefitImpliesPrivateInvestmentEarmarking : Bool
    institutionalComplianceFindingImpliesPerfectUnderlyingCompliance : Bool
open TaxIncidenceBoundary public

canonicalTaxIncidenceBoundary : TaxIncidenceBoundary
canonicalTaxIncidenceBoundary = tax-incidence-boundary
  true true true true true true true false false false false

data TaxBenefitImpliesImproperAct : Set where
data OfficialTenureImpliesPersonalResponsibility : Set where
data TaxBenefitImpliesEarmarkedInvestment : Set where
data InstitutionalComplianceImpliesPerfectReality : Set where

taxBenefitDoesNotCreateImproperAct : TaxBenefitImpliesImproperAct → ⊥
taxBenefitDoesNotCreateImproperAct ()

officialTenureDoesNotCreatePersonalResponsibility : OfficialTenureImpliesPersonalResponsibility → ⊥
officialTenureDoesNotCreatePersonalResponsibility ()

taxBenefitDoesNotCreateEarmarking : TaxBenefitImpliesEarmarkedInvestment → ⊥
taxBenefitDoesNotCreateEarmarking ()

institutionalComplianceDoesNotCreatePerfectReality : InstitutionalComplianceImpliesPerfectReality → ⊥
institutionalComplianceDoesNotCreatePerfectReality ()

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
    localEconomicObligationsShouldAlsoBeMeasured : Bool
open RetainedCapitalEffect public

canonicalRetainedCapitalEffect : RetainedCapitalEffect
canonicalRetainedCapitalEffect = retained-capital-effect
  true true false true true

------------------------------------------------------------------------
-- Remaining max-cut is quantitative incidence and certificate/version detail.
------------------------------------------------------------------------

data EDCDebt : Set where
  annualBenefitReconciliation : EDCDebt
  statutoryCertificateTerms : EDCDebt
  laterComplianceReviews : EDCDebt
  employmentPayrollAndLocalSpendIncidence : EDCDebt
  effectiveTaxRateReconstruction : EDCDebt
  postSettlementRepaymentIncidence : EDCDebt
  exactLocalGoodsServicesSubtotal1999to2006 : EDCDebt

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
    "Reconcile Financial Trust and Southern Trust benefits year-by-year to tax returns, certificates and EDC calculations rather than relying only on aggregate court-exhibit totals." ∷
  edc-acquisition employmentPayrollAndLocalSpendIncidence 100
    "Quantify wages/payroll, actual employee residency, local supplier payments and other USVI economic benefits against approximately USD219.8m Financial Trust tax benefit; headcount alone is not benefit incidence." ∷
  edc-acquisition statutoryCertificateTerms 99
    "Acquire every certificate/extension and exact exemption condition, including employment, local-investment and residency obligations." ∷
  edc-acquisition laterComplianceReviews 99
    "Resolve 2009-2012/termination compliance findings, deficiencies, waivers and corrective actions while keeping institutional approval distinct from substantive truth." ∷
  edc-acquisition effectiveTaxRateReconstruction 98
    "Reconstruct ordinary business income, tax paid and effective rates from primary returns/exhibits without mixing investment income, fee income and entity transfers." ∷
  edc-acquisition exactLocalGoodsServicesSubtotal1999to2006 98
    "Extract the detailed 1999-2006 goods/services schedule so the local-dollar subtotal is primary-paid rather than derived from the rounded 77% headline." ∷
  edc-acquisition postSettlementRepaymentIncidence 97
    "Trace later estate/USVI settlement repayments against historical benefits without treating civil settlement as admission beyond its terms." ∷
  []
