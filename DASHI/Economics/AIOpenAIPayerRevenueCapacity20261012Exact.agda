module DASHI.Economics.AIOpenAIPayerRevenueCapacity20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primaryFilingKind : Source.SourceKind
primaryFilingKind = Source.namedSourceKind "primary SEC filing"

secondaryFinancialReportingKind : Source.SourceKind
secondaryFinancialReportingKind = Source.namedSourceKind "secondary current financial reporting"

coreWeaveOpenAIContractSource : Source.AttributedSource
coreWeaveOpenAIContractSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Quarterly report for period ended June 30 2026"
  "SEC Form 10-Q"
  "2026-08-12"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm"
  primaryFilingKind
  "OpenAI commitment up to approximately USD 6.5B through May 31 2031; CoreWeave expects OpenAI to be a significant future customer"
  Source.publicAttribution

openAIRevenueSource : Source.AttributedSource
openAIRevenueSource = Source.mkNoDOISource
  "Reuters"
  "OpenAI's September annualized revenue nears $50 billion, less than previously indicated, source says"
  "current financial reporting"
  "2026-10-08"
  "https://www.reuters.com/business/openais-annualized-revenue-20-billion-less-than-previously-signaled-ft-reports-2026-10-08/"
  secondaryFinancialReportingKind
  "reports September annualised revenue near USD 50B and cautions that annualised revenue can be misleading; this is not an audited cash-flow statement"
  Source.publicAttribution

record OpenAIPayerCapacity : Set where
  constructor openai-payer-capacity
  field
    coreWeaveCommitmentMillionUSD : Nat
    annualizedRevenueMillionUSD : Nat
    namedContractEdgePaid : Bool
    revenueScaleCapacityPaid : Bool
    externalCustomerCashProvenancePaid : Bool
    operatingCashFlowPaid : Bool
    contractRealisationPaid : Bool
    realisedTopCustomerIdentityPaid : Bool

open OpenAIPayerCapacity public

openAICoreWeaveCapacity : OpenAIPayerCapacity
openAICoreWeaveCapacity = openai-payer-capacity
  6500 50000 true true false false false false

coreWeaveOpenAICommitmentMillionUSDIs6500 :
  coreWeaveCommitmentMillionUSD openAICoreWeaveCapacity ≡ 6500
coreWeaveOpenAICommitmentMillionUSDIs6500 = refl

openAIAnnualizedRevenueMillionUSDIs50000 :
  annualizedRevenueMillionUSD openAICoreWeaveCapacity ≡ 50000
openAIAnnualizedRevenueMillionUSDIs50000 = refl

revenueScaleCapacityObserved :
  revenueScaleCapacityPaid openAICoreWeaveCapacity ≡ true
revenueScaleCapacityObserved = refl

externalCustomerCashProvenancePaidIsFalse :
  externalCustomerCashProvenancePaid openAICoreWeaveCapacity ≡ false
externalCustomerCashProvenancePaidIsFalse = refl

contractRealisationPaidIsFalse :
  contractRealisationPaid openAICoreWeaveCapacity ≡ false
contractRealisationPaidIsFalse = refl

data RevenueImpliesCashProvenancePermission : Set where
data AnnualizedRevenueImpliesContractRealisationPermission : Set where
data ContractEdgeImpliesRealisedTopCustomerIdentityPermission : Set where

revenueDoesNotCreateCashProvenance : RevenueImpliesCashProvenancePermission → ⊥
revenueDoesNotCreateCashProvenance ()

annualizedRevenueDoesNotCreateContractRealisation :
  AnnualizedRevenueImpliesContractRealisationPermission → ⊥
annualizedRevenueDoesNotCreateContractRealisation ()

contractEdgeDoesNotCreateRealisedCustomerIdentity :
  ContractEdgeImpliesRealisedTopCustomerIdentityPermission → ⊥
contractEdgeDoesNotCreateRealisedCustomerIdentity ()

boundary : String
boundary =
  "OpenAI now has both a source-paid CoreWeave contract edge (up to USD 6.5B through May 2031) and secondary current revenue-scale evidence (September annualised revenue near USD 50B). This narrows payer-capacity uncertainty, but annualised revenue is not operating cash flow or audited external-customer cash provenance, and neither observation establishes realised CoreWeave contract cash or identifies the anonymous current top-customer shares."
