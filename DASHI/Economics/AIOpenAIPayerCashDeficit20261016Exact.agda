module DASHI.Economics.AIOpenAIPayerCashDeficit20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secondaryPrivateFinancialReporting : Source.SourceKind
secondaryPrivateFinancialReporting = Source.namedSourceKind "secondary reporting on private-company financial projection"

reutersOpenAICashSource : Source.AttributedSource
reutersOpenAICashSource = Source.mkNoDOISource
  "Reuters"
  "OpenAI forecasts cash burn near USD280 billion by 2030, FT reports"
  "secondary report of Financial Times report on private OpenAI presentation"
  "2026-09-18"
  "https://www.reuters.com/technology/openai-expects-burn-through-almost-280-billion-by-2030-ft-reports-2026-09-18/"
  secondaryPrivateFinancialReporting
  "reports a private-company projection of roughly USD278B cumulative negative free cash flow from 2026-2030, roughly USD856B compute/infrastructure spending through 2030, roughly USD36B 2026 revenue rising toward USD350B in 2030, and funding exhaustion risk by 2028; underlying private presentation is not public audited financial reporting"
  Source.publicAttribution

record OpenAIPayerCashDeficitBoundary : Set where
  constructor openai-payer-cash-deficit-boundary
  field
    reportedNegativeFCF2026to2030USDbn : Nat
    reportedComputeInfrastructureSpendTo2030USDbn : Nat
    reported2026RevenueUSDbn : Nat
    reported2030RevenueUSDbn : Nat
    reportedMarchFundingUSDbn : Nat
    reportedCashExhaustionYearWithoutFurtherFunding : Nat
    projectedOperatingSelfFundingGapObserved : Bool
    externalFinancingDependenceObserved : Bool
    auditedCashFlowPublic : Bool
    coreWeavePaymentsProvedSelfFundedByOperatingCash : Bool
    terminalPayerIndependenceEstablished : Bool
    insolvencyEstablished : Bool
    source : Source.AttributedSource

open OpenAIPayerCashDeficitBoundary public

openAICashDeficitBoundary : OpenAIPayerCashDeficitBoundary
openAICashDeficitBoundary = openai-payer-cash-deficit-boundary
  278 856 36 350 122 2028
  true true false false false false reutersOpenAICashSource

projectedCashDeficitPaid : projectedOperatingSelfFundingGapObserved openAICashDeficitBoundary ≡ true
projectedCashDeficitPaid = refl

coreWeavePaymentsStillNotSelfFunded : coreWeavePaymentsProvedSelfFundedByOperatingCash openAICashDeficitBoundary ≡ false
coreWeavePaymentsStillNotSelfFunded = refl

data RevenueScaleImpliesPositiveFCFPermission : Set where
data ProjectedBurnImpliesInsolvencyPermission : Set where
data ExternalFundingImpliesNonTerminalDemandPermission : Set where

revenueScaleDoesNotCreatePositiveFCF : RevenueScaleImpliesPositiveFCFPermission → ⊥
revenueScaleDoesNotCreatePositiveFCF ()

projectedBurnDoesNotCreateInsolvency : ProjectedBurnImpliesInsolvencyPermission → ⊥
projectedBurnDoesNotCreateInsolvency ()

externalFundingDoesNotByItselfCreateNonTerminalDemand : ExternalFundingImpliesNonTerminalDemandPermission → ⊥
externalFundingDoesNotByItselfCreateNonTerminalDemand ()

boundary : String
boundary =
  "Secondary reporting on a private OpenAI presentation materially narrows the payer question: very large reported revenue can coexist with a projected cumulative USD278B negative free-cash-flow requirement and roughly USD856B compute/infrastructure spending through 2030. This supports an external-financing-dependence coordinate and blocks revenue scale from being treated as self-funded terminal cash. It does not provide audited public cash flow, identify the source of each CoreWeave payment, establish terminal non-independence or establish insolvency."
