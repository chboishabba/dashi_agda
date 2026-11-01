module DASHI.Economics.ReflexiveFlowValidationExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- GENERIC ECONOMIC REFLEXIVITY / TERMINAL-PAYER CALCULUS
--
-- This module is intentionally domain-neutral.  It separates capital,
-- revenue, valuation, productive-service, manufacturing and policy flows.
-- A cycle across those layers is evidence of reflexivity, not by itself a
-- proof of fraud, invalid accounting, or economic non-viability.
------------------------------------------------------------------------

record EconomicFlowSystem : Set₁ where
  field
    Entity : Set
    CapitalFlow RevenueFlow ValuationExposure ProductiveFlow
      ManufacturingFlow PolicyFlow : Entity → Entity → Set

open EconomicFlowSystem public

record CapitalToCustomerCycle
    (sys : EconomicFlowSystem)
    (investor customer : Entity sys) : Set where
  field
    capitalToCustomer : CapitalFlow sys investor customer
    revenueBack       : RevenueFlow sys customer investor

record ValuationReflexivity
    (sys : EconomicFlowSystem)
    (investor investee : Entity sys) : Set where
  field
    financingExposure : CapitalFlow sys investor investee
    markedExposure    : ValuationExposure sys investor investee

-- Externality is relative to a declared financing/economic component.  It is
-- not inferred from corporate names, legal separateness, or geography.
record TerminalPayerPartition (sys : EconomicFlowSystem) : Set₁ where
  field
    ExternalPayer InternalEcosystemPayer : Entity sys → Set

open TerminalPayerPartition public

record ExternalCashReceipt
    (sys : EconomicFlowSystem)
    (partition : TerminalPayerPartition sys)
    (seller payer : Entity sys) : Set where
  field
    payerExternal : ExternalPayer partition payer
    cashRevenue   : RevenueFlow sys payer seller

record ExternalEconomicValidation
    (sys : EconomicFlowSystem)
    (partition : TerminalPayerPartition sys)
    (project : Entity sys) : Set₁ where
  field
    externalGrossProfit : Set
    depreciationPaid    : Set
    debtServicePaid     : Set
    requiredReturnPaid  : Set
    replacementCapexPaid : Set

open ExternalEconomicValidation public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FinancialConnectivityImpliesIndependentValidationPermission : Set where

data MarkedGainImpliesExternalCashPermission : Set where

data RevenueGrowthImpliesExternalViabilityPermission : Set where

financialConnectivityDoesNotAutoPromoteToIndependentValidation :
  FinancialConnectivityImpliesIndependentValidationPermission → ⊥
financialConnectivityDoesNotAutoPromoteToIndependentValidation ()

markedGainDoesNotAutoPromoteToExternalCash :
  MarkedGainImpliesExternalCashPermission → ⊥
markedGainDoesNotAutoPromoteToExternalCash ()

revenueGrowthDoesNotAutoPromoteToExternalViability :
  RevenueGrowthImpliesExternalViabilityPermission → ⊥
revenueGrowthDoesNotAutoPromoteToExternalViability ()
