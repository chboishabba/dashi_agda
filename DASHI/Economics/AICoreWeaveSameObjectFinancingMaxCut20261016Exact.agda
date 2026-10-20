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
import DASHI.Economics.AICoreWeaveOpenAIDDTL3CashHardwareWeld20261016Exact as OpenAIWeld
import DASHI.Economics.AICoreWeaveOpenAIContractRealisationCure20261016Exact as Cure
import DASHI.Economics.AIOpenAIContractRealisationTerminalCashNonDescent20261016Exact as NonDescent

record SameObjectFinancingStatus : Set where
  constructor same-object-financing-status
  field
    sameObjectDepreciationClock : Bool
    projectSpecificFinancingSurface : Bool
    customerCreditFinancingCoupling : Bool
    sameSPVFinanceToSiteMapping : Bool
    sameInstrumentCreditRepricing : Bool
    namedOpenAIContractCashArchitecture : Bool
    privateGPUIdentifierReportingRequired : Bool
    contractRealisationEquityCureMechanism : Bool
    covenantComplianceInsufficientForCustomerCash : Bool
    exactFinancedGPUCohort : Bool
    exactFinancedMW : Bool
    financedCustomerIdentity : Bool
    realisedProjectReturn : Bool
    realisedRefinancingTransaction : Bool
    namedTerminalCash : Bool
    publicSerialInventory : Bool
    realisedCustomerCashVsCureDecomposition : Bool

open SameObjectFinancingStatus public

coreWeaveSameObjectFinancingStatus : SameObjectFinancingStatus
coreWeaveSameObjectFinancingStatus = same-object-financing-status
  true true true true true true true true true
  false false false false false false false false

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

namedOpenAIContractCashArchitecturePaid : namedOpenAIContractCashArchitecture coreWeaveSameObjectFinancingStatus ≡ true
namedOpenAIContractCashArchitecturePaid = refl

privateGPUIdentifierReportingRequired : SameObjectFinancingStatus.privateGPUIdentifierReportingRequired coreWeaveSameObjectFinancingStatus ≡ true
privateGPUIdentifierReportingRequired = refl

contractRealisationEquityCureMechanismPaid :
  contractRealisationEquityCureMechanism coreWeaveSameObjectFinancingStatus ≡ true
contractRealisationEquityCureMechanismPaid = refl

covenantComplianceInsufficientForCustomerCashPaid :
  covenantComplianceInsufficientForCustomerCash coreWeaveSameObjectFinancingStatus ≡ true
covenantComplianceInsufficientForCustomerCashPaid = refl

exactFinancedGPUCohortStillOpen : exactFinancedGPUCohort coreWeaveSameObjectFinancingStatus ≡ false
exactFinancedGPUCohortStillOpen = refl

realisedProjectReturnStillOpen : realisedProjectReturn coreWeaveSameObjectFinancingStatus ≡ false
realisedProjectReturnStillOpen = refl

namedTerminalCashStillOpen : namedTerminalCash coreWeaveSameObjectFinancingStatus ≡ false
namedTerminalCashStillOpen = refl

publicRealisedNamedCashStillOpen : namedTerminalCash coreWeaveSameObjectFinancingStatus ≡ false
publicRealisedNamedCashStillOpen = refl

publicSerialInventoryStillOpen : publicSerialInventory coreWeaveSameObjectFinancingStatus ≡ false
publicSerialInventoryStillOpen = refl

realisedCustomerCashVsCureDecompositionStillOpen :
  realisedCustomerCashVsCureDecomposition coreWeaveSameObjectFinancingStatus ≡ false
realisedCustomerCashVsCureDecompositionStillOpen = refl

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

openAINamedMSAPinned : OpenAIWeld.openAIPhoenix1NamedMSA OpenAIWeld.coreWeaveOpenAIDDTL3CashHardwareWeld ≡ true
openAINamedMSAPinned = OpenAIWeld.openAIPhoenix1NamedMSAPaid

privateSerialReportingPinned : OpenAIWeld.gpuRackSerialReportingRequirement OpenAIWeld.coreWeaveOpenAIDDTL3CashHardwareWeld ≡ true
privateSerialReportingPinned = OpenAIWeld.gpuRackSerialReportingRequirementPaid

equityCureMechanismPinned : Cure.unlimitedEquityCuresBefore20261028 Cure.coreWeaveOpenAIContractRealisationCure ≡ true
equityCureMechanismPinned = Cure.unlimitedEquityCuresThrough20261027Paid

covenantNonDescentPinned :
  NonDescent.covenantObserver NonDescent.customer85 ≡ NonDescent.covenantObserver NonDescent.customer80Cure5
covenantNonDescentPinned = NonDescent.sameCompliantCovenantObservation

boundary : String
boundary =
  "The CoreWeave financing max-cut has moved from company-level proxies to several same-object joins. Primary credit agreements pay contractual GPU depreciation of roughly 66-78 months rather than a CoreWeave-specific 36-48 month life; disclosed DDTLs pay project/customer-specific spread terms; DDTL 2.0 and 4.0 expose direct customer-credit/capex-to-financing mechanics; the DDTL 4.0 borrower SPV is source-joined to identified Polaris Forge 1 lease space; and the 9.625 percent 2032 notes have a same-instrument October secondary-market repricing above 15 percent. DDTL 3.0 additionally identifies OpenAI/Phoenix 1, places actual customer cash/MSA payment rights inside the financing cash-control surface, defines a contract-realisation ratio and requires GPU-rack serial reporting to lenders. Its amendment permits equity-cure proceeds to enter the Contract Realization Ratio numerator. Canonical non-descent therefore blocks covenant compliance from identifying terminal customer cash unless customer billings/receipts are separated from cure proceeds. Exact cash and hardware identifiers are contractually measured/reported inside this financing surface, but public filings do not disclose their realised values. The remaining authority wall is public customer-cash-versus-cure decomposition, public serial/GPU inventory, exact financed MW/generation/count, realised project return and realised refinancing outcomes."
