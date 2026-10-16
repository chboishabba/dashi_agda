module DASHI.Economics.AICapitalPhase2Acquisition20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICoreWeaveCreditDeterioration20261016Exact as Credit
import DASHI.Economics.AICoreWeave2032BondRepricing20261016Exact as Bond
import DASHI.Economics.AICoreWeaveOpenAIDDTL3CashHardwareWeld20261016Exact as OpenAIWeld
import DASHI.Economics.AICoreWeaveOpenAIContractRealisationCure20261016Exact as Cure
import DASHI.Economics.AIOpenAIContractRealisationTerminalCashNonDescent20261016Exact as CashNonDescent
import DASHI.Economics.AIOpenAIPayerCashDeficit20261016Exact as OpenAI
import DASHI.Economics.AIAustraliaOperativeAIPolicyBaseline20261016Exact as Policy
import DASHI.Economics.AICoreWeaveSecondaryMarketResidualValue20261016Exact as Residual
import DASHI.Economics.AICapitalOutcomeSignatures20261016Exact as Outcome

record Phase2AcquisitionState : Set where
  constructor phase2-acquisition-state
  field
    issuerCreditTrajectoryPaid : Bool
    sameInstrumentCreditRepricingPaid : Bool
    payerFinancingDependencePaid : Bool
    namedOpenAIContractMeasurementArchitecturePaid : Bool
    privateGPUIdentifierReportingRequired : Bool
    contractRealisationEquityCureMechanismPaid : Bool
    covenantComplianceInsufficientForCustomerCashPaid : Bool
    commercialResidualProxyPaid : Bool
    operativeAustralianPolicyBaselinePaid : Bool
    actualDefaultPaid : Bool
    namedCoreWeavePaymentCashPaid : Bool
    publicNamedOpenAICashPaid : Bool
    publicSerialInventoryPaid : Bool
    realisedCustomerCashVsCureDecompositionPaid : Bool
    coreWeaveRealisedHardwareResidualPaid : Bool
    realisedRefinancingTransactionPaid : Bool
    realisedMandatoryPolicyCostPaid : Bool
    terminalOutcomePromoted : Bool

open Phase2AcquisitionState public

currentPhase2AcquisitionState : Phase2AcquisitionState
currentPhase2AcquisitionState = phase2-acquisition-state
  true true true true true true true true true
  false false false false false false false false false

newCoordinatesPaid :
  (issuerCreditTrajectoryPaid currentPhase2AcquisitionState ≡ true) ×
  (sameInstrumentCreditRepricingPaid currentPhase2AcquisitionState ≡ true) ×
  (payerFinancingDependencePaid currentPhase2AcquisitionState ≡ true) ×
  (namedOpenAIContractMeasurementArchitecturePaid currentPhase2AcquisitionState ≡ true) ×
  (privateGPUIdentifierReportingRequired currentPhase2AcquisitionState ≡ true)
newCoordinatesPaid = refl , refl , refl , refl , refl

sameInstrumentCreditRepricingIsPaid :
  Bond.sameInstrumentLongitudinalRepricing Bond.coreWeave2032BondRepricing ≡ true
sameInstrumentCreditRepricingIsPaid = Bond.sameInstrumentLongitudinalRepricingPaid

openAIContractMeasurementArchitectureIsPaid :
  OpenAIWeld.contractRealisationRatioMechanism OpenAIWeld.coreWeaveOpenAIDDTL3CashHardwareWeld ≡ true
openAIContractMeasurementArchitectureIsPaid = OpenAIWeld.contractRealisationRatioMechanismPaid

privateGPUIdentifiersRequired :
  OpenAIWeld.gpuRackSerialReportingRequirement OpenAIWeld.coreWeaveOpenAIDDTL3CashHardwareWeld ≡ true
privateGPUIdentifiersRequired = OpenAIWeld.gpuRackSerialReportingRequirementPaid

contractRealisationEquityCureMechanismPaid :
  Cure.unlimitedEquityCuresBefore20261028 Cure.coreWeaveOpenAIContractRealisationCure ≡ true
contractRealisationEquityCureMechanismPaid = Cure.unlimitedEquityCuresThrough20261027Paid

covenantComplianceInsufficientForCustomerCashPaid :
  (CashNonDescent.covenantObserver CashNonDescent.customer85 ≡
   CashNonDescent.covenantObserver CashNonDescent.customer80Cure5)
covenantComplianceInsufficientForCustomerCashPaid = CashNonDescent.sameCompliantCovenantObservation

publicNamedOpenAICashPaidIsFalse : publicNamedOpenAICashPaid currentPhase2AcquisitionState ≡ false
publicNamedOpenAICashPaidIsFalse = refl

publicSerialInventoryPaidIsFalse : publicSerialInventoryPaid currentPhase2AcquisitionState ≡ false
publicSerialInventoryPaidIsFalse = refl

realisedCustomerCashVsCureDecompositionPaidIsFalse :
  realisedCustomerCashVsCureDecompositionPaid currentPhase2AcquisitionState ≡ false
realisedCustomerCashVsCureDecompositionPaidIsFalse = refl

outcomeStillNotPromoted : terminalOutcomePromoted currentPhase2AcquisitionState ≡ false
outcomeStillNotPromoted = refl

outcomeOwnerAlsoOpen : Outcome.currentOutcomePromotionReady ≡ false
outcomeOwnerAlsoOpen = refl

boundary : String
boundary =
  "The October-16 Phase-2 acquisition pass now distinguishes public absence, private measurement and a repaired measurement requirement. CoreWeave has same-issuer CDS deterioration and a stronger same-instrument 2032-note repricing. DDTL 3.0 proves that named OpenAI/Phoenix 1 customer-cash, contract-realisation and GPU-rack serial identifiers exist inside the lender control surface; its amendment further permits equity cure proceeds to enter the Contract Realization Ratio numerator. Canonical non-descent therefore proves that even a compliant CRR cannot identify customer cash unless customer billings/receipts are separated from cure proceeds. Commercial residual-value proxies and the Australian operative-policy baseline remain separately typed. The public residual is now specific: realised OpenAI customer cash vs cure decomposition, public hardware identifiers, CoreWeave realised hardware residual proceeds, realised refinancing transactions, actual default/restructuring, realised mandatory actor-class compliance costs and repeated comparable state observations."
