module DASHI.Economics.AITerminalPayerEconomicValidationExact where

open import DASHI.Core.Prelude
import DASHI.Economics.ReflexiveFlowValidationExact as Econ

------------------------------------------------------------------------
-- TERMINAL-PAYER VALIDATION FOR AI INFRASTRUCTURE
------------------------------------------------------------------------

record AITerminalPayerSystem : Set₁ where
  field
    flowSystem : Econ.EconomicFlowSystem
    partition  : Econ.TerminalPayerPartition flowSystem

open AITerminalPayerSystem public

record IncrementalAIInfrastructureEconomicallyValidated
    (sys : AITerminalPayerSystem)
    (project : Econ.Entity (flowSystem sys)) : Set₁ where
  field
    externalValidation :
      Econ.ExternalEconomicValidation (flowSystem sys) (partition sys) project

open IncrementalAIInfrastructureEconomicallyValidated public

record ExternalAIDemandExists
    (sys : AITerminalPayerSystem)
    (seller payer : Econ.Entity (flowSystem sys)) : Set where
  field
    externalCash : Econ.ExternalCashReceipt (flowSystem sys) (partition sys) seller payer

-- The top-level firewall: demand, growth, utilisation, scarcity, marked gains,
-- and policy support are all evidence around viability.  None individually or
-- as an untyped bundle manufactures the terminal-payer validation receipt.
record SurroundingAISuccessSignals : Set₁ where
  field
    ExternalDemand RevenueGrowth HighUtilisation HardwareScarcity
      InvestmentGains PolicySupport : Set
    externalDemand : ExternalDemand
    revenueGrowth  : RevenueGrowth
    highUtilisation : HighUtilisation
    hardwareScarcity : HardwareScarcity
    investmentGains : InvestmentGains
    policySupport : PolicySupport

open SurroundingAISuccessSignals public

data SurroundingSignalsImplyEconomicValidationPermission : Set where

surroundingSignalsDoNotAutoPromoteToEconomicValidation :
  SurroundingSignalsImplyEconomicValidationPermission → ⊥
surroundingSignalsDoNotAutoPromoteToEconomicValidation ()

revenueGrowthDoesNotCloseExternalViability :
  Econ.RevenueGrowthImpliesExternalViabilityPermission → ⊥
revenueGrowthDoesNotCloseExternalViability =
  Econ.revenueGrowthDoesNotAutoPromoteToExternalViability
