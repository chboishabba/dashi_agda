module DASHI.Economics.AICoreWeaveAssetLevelContractFinance20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primaryCompanyFiling : Source.SourceKind
primaryCompanyFiling = Source.namedSourceKind "primary SEC-filed company financing presentation"

coreWeaveFinancingSource : Source.AttributedSource
coreWeaveFinancingSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "2026 Convertible Notes Investor Presentation"
  "SEC-filed financing presentation"
  "2026-09"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000429/crwv2026convertpresentat.htm"
  primaryCompanyFiling
  "states asset-level financing funds the majority of capex, is secured by long-term take-or-pay customer contracts plus related GPUs/PP&E/data-center leases, typically amortizes as contractual customer payments arrive so debt is fully repaid by contract expiry, and can receive investment-grade ratings when underlying customers are investment grade"
  Source.publicAttribution

record AssetLevelContractFinance : Set where
  constructor asset-level-contract-finance
  field
    majorityCapexAssetLevelFinance : Bool
    securedByTakeOrPayContracts : Bool
    relatedAssetsCollateralised : Bool
    amortisesWithCustomerPayments : Bool
    targetDebtRepaidByContractExpiry : Bool
    investmentGradeCustomerLookthrough : Bool
    customerPrepaymentsParentFundingSource : Bool
    terminalCustomerCashIndependencePaid : Bool
    contractRealisationPaid : Bool
    financingEliminatesSystemCapitalBurden : Bool

open AssetLevelContractFinance public

coreWeaveAssetLevelFinance : AssetLevelContractFinance
coreWeaveAssetLevelFinance = asset-level-contract-finance
  true true true true true true true false false false

majorityCapexAssetLevelFinanced :
  majorityCapexAssetLevelFinance coreWeaveAssetLevelFinance ≡ true
majorityCapexAssetLevelFinanced = refl

contractAmortisationStructureObserved :
  amortisesWithCustomerPayments coreWeaveAssetLevelFinance ≡ true
contractAmortisationStructureObserved = refl

investmentGradeCustomerLookthroughObserved :
  investmentGradeCustomerLookthrough coreWeaveAssetLevelFinance ≡ true
investmentGradeCustomerLookthroughObserved = refl

data FinancingStructureImpliesTerminalDemandPermission : Set where
data ContractSecuredDebtImpliesContractRealisationPermission : Set where
data AssetLevelFinanceImpliesNoSystemCapitalBurdenPermission : Set where

financingStructureDoesNotCreateTerminalDemand :
  FinancingStructureImpliesTerminalDemandPermission → ⊥
financingStructureDoesNotCreateTerminalDemand ()

contractSecurityDoesNotCreateRealisation :
  ContractSecuredDebtImpliesContractRealisationPermission → ⊥
contractSecurityDoesNotCreateRealisation ()

assetLevelFinanceDoesNotEraseSystemCapitalBurden :
  AssetLevelFinanceImpliesNoSystemCapitalBurdenPermission → ⊥
assetLevelFinanceDoesNotEraseSystemCapitalBurden ()

boundary : String
boundary =
  "CoreWeave's SEC-filed financing presentation pays a concrete contract-finance mechanism: asset-level facilities fund most capex, are secured by long-term take-or-pay contracts and associated infrastructure, and are designed to amortise with customer payments through contract expiry; investment-grade customer credit can support investment-grade facility ratings. This is strong financing-structure evidence, not proof of terminal-customer cash independence, realised contract payments, or disappearance of ecosystem capital burden."
