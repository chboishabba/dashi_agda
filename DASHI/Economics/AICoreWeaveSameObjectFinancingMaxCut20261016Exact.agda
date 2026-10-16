module DASHI.Economics.AICoreWeaveSameObjectFinancingMaxCut20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICoreWeaveSameObjectFinancingClock20261016Exact as Clock
import DASHI.Economics.AICoreWeaveContractBackedFinancingSurface20261016Exact as Surface
import DASHI.Economics.AICoreWeaveCustomerCreditFinancingCoupling20261016Exact as Coupling
import DASHI.Economics.AICoreWeaveDDTL4PolarisForgeMapping20261016Exact as Mapping
import DASHI.Economics.AICoreWeave2032BondRepricing20261016Exact as Repricing

record SameObjectFinancingStatus : Set where
  constructor same-object-financing-status
  field
    sameObjectDepreciationClock : Bool
    projectSpecificFinancingSurface : Bool
    customerCreditFinancingCoupling : Bool
    sameSPVFinanceToSiteMapping : Bool
    sameInstrumentCreditRepricing : Bool
    exactFinancedGPUCohort : Bool
    exactFinancedMW : Bool
    financedCustomerIdentity : Bool
    realisedProjectReturn : Bool
    realisedRefinancingTransaction : Bool
    namedTerminalCash : Bool

open SameObjectFinancingStatus public

coreWeaveSameObjectFinancingStatus : SameObjectFinancingStatus
coreWeaveSameObjectFinancingStatus = same-object-financing-status
  true true true true true
  false false false false false false

sameObjectDepreciationClockPaid : sameObjectDepreciationClock coreWeaveSameObjectFinancingStatus ≡ true
sameObjectDepreciationClockPaid = refl

projectSpecificFinancingSurfacePaid : projectSpecificFinancingSurface coreWeaveSameObjectFinancingStatus ≡ true
projectSpecificFinancingSurfacePaid = refl

customerCreditFinancingCouplingPaid : customerCreditFinancingCoupling coreWeaveSameObjectFinancingStatus ≡ true
customerCreditFinancingCouplingPaid = refl

sameSPVFinanceToSiteMappingPaid : sameSPVFinanceToSiteMapping coreWeaveSameObjectFinancingStatus ≡ true
sameSPVFinanceToSiteMappingPaid = refl

sameInstrumentCreditRepricingPaid : sameInstrumentCreditRepricing coreWeaveSameObjectFinancingStatus ≡ true
sameInstrumentCreditRepricingPaid = refl

exactFinancedGPUCohortStillOpen : exactFinancedGPUCohort coreWeaveSameObjectFinancingStatus ≡ false
exactFinancedGPUCohortStillOpen = refl

realisedProjectReturnStillOpen : realisedProjectReturn coreWeaveSameObjectFinancingStatus ≡ false
realisedProjectReturnStillOpen = refl

namedTerminalCashStillOpen : namedTerminalCash coreWeaveSameObjectFinancingStatus ≡ false
namedTerminalCashStillOpen = refl

clockCorrectionPinned : Clock.old24To36MonthMismatchPromotable Clock.coreWeaveSameObjectFinancingClock ≡ false
clockCorrectionPinned = Clock.old24To36MonthMismatchNotPromotable

projectRateHeterogeneityPinned :
  (Surface.sofrMarginBp Surface.ddtl3 ≡ 400) ×
  (Surface.sofrMarginBp Surface.ddtl4 ≡ 225) ×
  (Surface.sofrMarginBp Surface.ddtl5 ≡ 450) ×
  (Surface.sofrMarginBp Surface.ddtl55 ≡ 550)
projectRateHeterogeneityPinned = refl , refl , refl , refl

customerCreditTransmissionPinned : Coupling.customerCreditTransmitsIntoFinancingTerms Coupling.coreWeaveCustomerCreditFinancing ≡ true
customerCreditTransmissionPinned = Coupling.customerCreditTransmitsIntoFinancingTermsReceipt

sameSiteSPVPinned : Mapping.sameBorrowerSPV Mapping.coreWeaveDDTL4PolarisForgeMapping ≡ true
sameSiteSPVPinned = Mapping.sameBorrowerSPVIsPaid

sameInstrumentRepricingPinned : Repricing.sameInstrumentLongitudinalRepricing Repricing.coreWeave2032BondRepricing ≡ true
sameInstrumentRepricingPinned = Repricing.sameInstrumentLongitudinalRepricingPaid

boundary : String
boundary =
  "The CoreWeave financing max-cut has moved from company-level proxies to several same-object joins. Primary credit agreements pay contractual GPU depreciation of roughly 66-78 months rather than a CoreWeave-specific 36-48 month life; disclosed DDTLs pay project/customer-specific spread terms; DDTL 2.0 and 4.0 expose direct customer-credit/capex-to-financing mechanics; the DDTL 4.0 borrower SPV is source-joined to identified Polaris Forge 1 lease space; and the 9.625 percent 2032 notes have a same-instrument October secondary-market repricing above 15 percent. The remaining authority wall is narrower: exact financed GPU generation/count/MW, associated customer identity, realised project return, realised refinancing transactions and named terminal customer cash. None of the paid structural/market coordinates creates those missing cash-return facts."
