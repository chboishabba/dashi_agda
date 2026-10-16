module DASHI.Economics.AICoreWeaveDemandDistressNonCollapse20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

companyPressKind : Source.SourceKind
companyPressKind = Source.namedSourceKind "company investor-relations release"

secondaryMarketReportingKind : Source.SourceKind
secondaryMarketReportingKind = Source.namedSourceKind "secondary financial-market reporting"

coreWeavePricingDemandSource : Source.AttributedSource
coreWeavePricingDemandSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "CoreWeave Continues to Contract New Compute Capacity at Higher Prices"
  "investor-relations release"
  "2026-09-17"
  "https://investors.coreweave.com/news/news-details/2026/CoreWeave-Continues-to-Contract-New-Compute-Capacity-at-Higher-Prices/default.aspx"
  companyPressKind
  "company-reported Q3 short-dated three-to-six-month customer contracts at about USD 40M per MW annualised; more than USD 25B net new customer commitments early Q3; total contracted power about 4.2 GW as of 2026-08-11"
  Source.publicAttribution

coreWeaveMarketDistressSource : Source.AttributedSource
coreWeaveMarketDistressSource = Source.mkNoDOISource
  "Reuters"
  "CoreWeave's AI contracts and the lenders financing its build-out"
  "financial-market report"
  "2026-10-15"
  "https://www.reuters.com/legal/transactional/coreweaves-ai-contracts-lenders-financing-its-build-out-2026-10-15/"
  secondaryMarketReportingKind
  "reports approximately USD 50B debt and a market-implied five-year default probability around 63 percent from CoreWeave CDS while also describing large contracted customer demand and lender exposures"
  Source.publicAttribution

record DemandDistressState : Set where
  constructor demand-distress-state
  field
    shortDatedAnnualizedRevenuePerMWMillionUSD : Nat
    contractedPowerMW : Nat
    earlyQ3NetNewCommitmentsBillionUSDLowerBound : Nat
    reportedDebtBillionUSDApprox : Nat
    reportedFiveYearDefaultProbabilityPercentApprox : Nat
    strongDemandCoordinatePaid : Bool
    marketDistressCoordinatePaid : Bool
    demandImpliesCapitalRecovery : Bool
    demandImpliesSolvency : Bool
    distressImpliesNoDemand : Bool
    defaultOccurred : Bool
    bubbleEstablished : Bool

open DemandDistressState public

currentDemandDistressState : DemandDistressState
currentDemandDistressState = demand-distress-state
  40 4200 25 50 63 true true false false false false false

demandAndDistressCoexist :
  (strongDemandCoordinatePaid currentDemandDistressState ≡ true) ×
  (marketDistressCoordinatePaid currentDemandDistressState ≡ true)
demandAndDistressCoexist = refl , refl

data DemandImpliesCapitalRecoveryPermission : Set where
data DemandImpliesSolvencyPermission : Set where
data DistressImpliesNoDemandPermission : Set where
data CDSProbabilityEqualsDefaultPermission : Set where
data MarketDistressEqualsBubblePermission : Set where

demandDoesNotCreateCapitalRecovery : DemandImpliesCapitalRecoveryPermission → ⊥
demandDoesNotCreateCapitalRecovery ()

demandDoesNotCreateSolvency : DemandImpliesSolvencyPermission → ⊥
demandDoesNotCreateSolvency ()

distressDoesNotEraseDemand : DistressImpliesNoDemandPermission → ⊥
distressDoesNotEraseDemand ()

cdsProbabilityDoesNotEqualDefault : CDSProbabilityEqualsDefaultPermission → ⊥
cdsProbabilityDoesNotEqualDefault ()

marketDistressDoesNotEstablishBubble : MarketDistressEqualsBubblePermission → ⊥
marketDistressDoesNotEstablishBubble ()

boundary : String
boundary =
  "The same CoreWeave object now carries independently sourced strong-demand and market-distress coordinates. Company reporting pays short-dated ~USD40M/MW annualised pricing, >USD25B early-Q3 commitments and ~4.2GW contracted power. Reuters reports ~USD50B debt and a CDS-implied five-year default probability around 63 percent. Their coexistence is evidence that demand/backlog does not by itself pay capital recovery or solvency. CDS-implied probability is a market price, not an occurred default, and the conjunction is not a bubble theorem."
