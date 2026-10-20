module DASHI.Economics.AICapitalSOTAReconciliation20261016Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Economics.AICoreWeaveDemandDistressNonCollapse20261016Exact as Demand
import DASHI.Economics.AIOpenWeightProductionSubstitution20261016Exact as Open
import DASHI.Economics.AIEnergyCapitalBottleneck20261016Exact as Energy
import DASHI.Economics.AIAustraliaGuardrailsRetrenchment20261016Exact as Policy

-- RED-first integration surface for the 16-Oct-2026 SOTA tranche.
-- Each fixture is deliberately claim-relative; none is a bubble/capture theorem.

coreWeaveDemandAndDistressCoexist :
  (Demand.strongDemandCoordinatePaid Demand.currentDemandDistressState ≡ true) ×
  (Demand.marketDistressCoordinatePaid Demand.currentDemandDistressState ≡ true)
coreWeaveDemandAndDistressCoexist = Demand.demandAndDistressCoexist

openWeightSeptemberTokenShareIs715Permille :
  Open.openWeightTokenSharePermille Open.septemberGatewayProductionIndex ≡ 715
openWeightSeptemberTokenShareIs715Permille = refl

openWeightSeptemberSpendShareIs230Permille :
  Open.openWeightSpendSharePermille Open.septemberGatewayProductionIndex ≡ 230
openWeightSeptemberSpendShareIs230Permille = refl

hyperscalerCapexFloorIs700BillionUSD :
  Energy.hyperscalerCapexBillionUSDLowerBound Energy.currentEnergyCapitalBottleneck ≡ 700
hyperscalerCapexFloorIs700BillionUSD = refl

australiaMandatoryGuardrailsProceedingIsFalse :
  Policy.mandatoryGuardrailsProceeding Policy.currentAustralianGuardrailsState ≡ false
australiaMandatoryGuardrailsProceedingIsFalse = refl
