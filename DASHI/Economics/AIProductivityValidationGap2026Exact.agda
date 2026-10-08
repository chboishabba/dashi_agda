module DASHI.Economics.AIProductivityValidationGap2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.AITerminalPayerEconomicValidationExact as Terminal
import DASHI.Economics.AIOpenClosedGrowthCapitalRecoveryExact as Growth

------------------------------------------------------------------------
-- PRODUCTIVITY / CAPITAL-RECOVERY SEPARATION
--
-- Economy-wide productivity gains are one possible terminal-revenue producer,
-- but observed capability, adoption or local task productivity does not itself
-- close the amount/timing of cash required to service the current AI-capital
-- stack.
------------------------------------------------------------------------

record ProductivityTransmissionState : Set₁ where
  field
    CapabilityGain TaskProductivityGain FirmProfitGain EconomyProductivityGain : Set
    capabilityGain : CapabilityGain
    taskProductivityGain : TaskProductivityGain
    firmProfitGain : FirmProfitGain
    economyProductivityGain : EconomyProductivityGain

record CapitalPayoffRequirement : Set₁ where
  field
    IncrementalExternalCash DebtService Depreciation ReplacementCapex RequiredReturn : Set
    incrementalExternalCash : IncrementalExternalCash
    debtService : DebtService
    depreciation : Depreciation
    replacementCapex : ReplacementCapex
    requiredReturn : RequiredReturn


data CapabilityImpliesEconomyProductivityPermission : Set where
data ProductivityGainImpliesSufficientCapitalPayoffPermission : Set where
data AdoptionImpliesTerminalValidationPermission : Set where

capabilityDoesNotAutoProveEconomyProductivity :
  CapabilityImpliesEconomyProductivityPermission → ⊥
capabilityDoesNotAutoProveEconomyProductivity ()

productivityGainDoesNotAutoProveSufficientCapitalPayoff :
  ProductivityGainImpliesSufficientCapitalPayoffPermission → ⊥
productivityGainDoesNotAutoProveSufficientCapitalPayoff ()

adoptionDoesNotAutoProveTerminalValidation :
  AdoptionImpliesTerminalValidationPermission → ⊥
adoptionDoesNotAutoProveTerminalValidation ()

surroundingSignalsStillNeedTerminalReceipt :
  Terminal.SurroundingSignalsImplyEconomicValidationPermission → ⊥
surroundingSignalsStillNeedTerminalReceipt =
  Terminal.surroundingSignalsDoNotAutoPromoteToEconomicValidation
