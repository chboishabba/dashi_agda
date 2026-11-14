module DASHI.Economics.AICapitalSOTAReconciliation20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICoreWeaveDemandDistressNonCollapse20261016Exact as Demand
import DASHI.Economics.AIOpenWeightProductionSubstitution20261016Exact as Open
import DASHI.Economics.AIEnergyCapitalBottleneck20261016Exact as Energy
import DASHI.Economics.AIAustraliaGuardrailsRetrenchment20261016Exact as Policy

record SOTAReconciliation : Set where
  constructor sota-reconciliation
  field
    strongAIDemandObserved : Bool
    marketDistressObserved : Bool
    fallingUnitPriceWithSpendGrowthObserved : Bool
    openWeightProductionSubstitutionObserved : Bool
    physicalBuildoutObserved : Bool
    capitalMarketDependenceObserved : Bool
    australianMandatoryGuardrailsCurrentlyProceeding : Bool
    demandEqualsCapitalRecovery : Bool
    physicalBuildoutEqualsInvestorReturn : Bool
    openWeightUsageEqualsSelfHosting : Bool
    policyProposalEqualsOperativeBurden : Bool
    bubbleEstablished : Bool
    regulatoryCaptureEstablished : Bool

open SOTAReconciliation public

currentSOTAReconciliation : SOTAReconciliation
currentSOTAReconciliation = sota-reconciliation
  true true true true true true false
  false false false false false false

centralNonCollapsePaid :
  (strongAIDemandObserved currentSOTAReconciliation ≡ true) ×
  (marketDistressObserved currentSOTAReconciliation ≡ true) ×
  (fallingUnitPriceWithSpendGrowthObserved currentSOTAReconciliation ≡ true) ×
  (physicalBuildoutObserved currentSOTAReconciliation ≡ true)
centralNonCollapsePaid = refl , refl , refl , refl

bubbleStillNotEstablished : bubbleEstablished currentSOTAReconciliation ≡ false
bubbleStillNotEstablished = refl

regulatoryCaptureStillNotEstablished : regulatoryCaptureEstablished currentSOTAReconciliation ≡ false
regulatoryCaptureStillNotEstablished = refl

boundary : String
boundary =
  "October-2026 SOTA now supplies a four-sided falsification surface. Strong CoreWeave demand/contracts coexist with severe market-implied credit distress; Vercel production telemetry shows rapid spend/volume growth alongside falling average token prices and high open-weight token share; IEA evidence confirms a massive physical/electricity buildout that increasingly depends on capital markets while retaining profitability uncertainty; Australia supplies a negative/control policy observation because the earlier mandatory-guardrails proposal is not proceeding at this time. These jointly strengthen non-collapse: demand != capital recovery, physical buildout != investor return, open-weight hosted usage != self-hosting, and proposal != operative burden. They do not by themselves prove an AI bubble or intentional regulatory capture."
