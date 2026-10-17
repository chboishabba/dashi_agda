module DASHI.Economics.AICoreWeaveOpenAIDDTL3CashHardwareWeld20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secCreditKind : Source.SourceKind
secCreditKind = Source.namedSourceKind "SEC-filed credit agreement"

coreWeaveDDTL3OpenAISource : Source.AttributedSource
coreWeaveDDTL3OpenAISource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Credit Agreement dated July 28 2025 — CoreWeave Compute Acquisition Co. VII / V"
  "SEC-filed DDTL 3.0 credit agreement"
  "2025-07-28"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962825000033/coreweave30-ex101xtermlo.htm"
  secCreditKind
  "USD2.6B delayed-draw facility; Master Services Agreement is CoreWeave/OpenAI OpCo Phoenix 1; Available Cash is actual customer cash received; MSA payment rights and collateral accounts secure the obligations; contract-realisation ratio compares billed/received amounts with projected contracted cash flows; borrowers must provide GPU-rack serial numbers after borrowings"
  Source.publicAttribution

record OpenAIDDTL3CashHardwareWeld : Set where
  constructor openai-ddtl3-cash-hardware-weld
  field
    facilityCommitmentMillionUSD : Nat
    openAIPhoenix1NamedMSA : Bool
    availableCashDefinitionIsActualCustomerCash : Bool
    msaPaymentRightsAreCollateral : Bool
    collateralAccountReceivesMSARevenue : Bool
    contractRealisationRatioMechanism : Bool
    gpuRackSerialReportingRequirement : Bool
    publicRealisedOpenAICashAmount : Bool
    publicContractRealisationRatioValue : Bool
    publicGPUInventory : Bool
    publicSerialNumberRegister : Bool
    openAICreditQualityFullyObserved : Bool

open OpenAIDDTL3CashHardwareWeld public

coreWeaveOpenAIDDTL3CashHardwareWeld : OpenAIDDTL3CashHardwareWeld
coreWeaveOpenAIDDTL3CashHardwareWeld = openai-ddtl3-cash-hardware-weld
  2600 true true true true true true
  false false false false false

openAIPhoenix1NamedMSAPaid : openAIPhoenix1NamedMSA coreWeaveOpenAIDDTL3CashHardwareWeld ≡ true
openAIPhoenix1NamedMSAPaid = refl

availableCashDefinitionIsActualCustomerCash :
  OpenAIDDTL3CashHardwareWeld.availableCashDefinitionIsActualCustomerCash coreWeaveOpenAIDDTL3CashHardwareWeld ≡ true
availableCashDefinitionIsActualCustomerCash = refl

msaPaymentRightsAreCollateralPaid : msaPaymentRightsAreCollateral coreWeaveOpenAIDDTL3CashHardwareWeld ≡ true
msaPaymentRightsAreCollateralPaid = refl

contractRealisationRatioMechanismPaid : contractRealisationRatioMechanism coreWeaveOpenAIDDTL3CashHardwareWeld ≡ true
contractRealisationRatioMechanismPaid = refl

gpuRackSerialReportingRequirementPaid : gpuRackSerialReportingRequirement coreWeaveOpenAIDDTL3CashHardwareWeld ≡ true
gpuRackSerialReportingRequirementPaid = refl

publicRealisedOpenAICashAmountStillOpen : publicRealisedOpenAICashAmount coreWeaveOpenAIDDTL3CashHardwareWeld ≡ false
publicRealisedOpenAICashAmountStillOpen = refl

publicGPUInventoryStillOpen : publicGPUInventory coreWeaveOpenAIDDTL3CashHardwareWeld ≡ false
publicGPUInventoryStillOpen = refl

data ContractCashArchitectureCreatesRealisedCashPermission : Set where
data PrivateSerialReportingCreatesPublicInventoryPermission : Set where

contractCashArchitectureDoesNotCreateRealisedCash : ContractCashArchitectureCreatesRealisedCashPermission → ⊥
contractCashArchitectureDoesNotCreateRealisedCash ()

serialReportingRequirementDoesNotCreatePublicInventory : PrivateSerialReportingCreatesPublicInventoryPermission → ⊥
serialReportingRequirementDoesNotCreatePublicInventory ()

boundary : String
boundary =
  "CoreWeave DDTL 3.0 pays a unusually literal named customer-finance weld. The filed agreement identifies OpenAI OpCo's Phoenix 1 MSA, defines Available Cash as cash actually received from the customer, grants lender collateral rights in MSA payment rights and collateral accounts, defines a Contract Realization Ratio from amounts billed/received versus projected contracted cash flows, and requires GPU-rack serial numbers to be delivered to lenders after borrowings. This establishes that named contract cash and exact financed-hardware identifiers exist inside the financing control surface. The public filing does not disclose the realised OpenAI cash amounts, realised ratio values, serial-number inventory, exact GPU generations/counts, or OpenAI's full credit condition. Contract architecture/private reporting obligations therefore do not become public realised terminal-cash or hardware receipts."
