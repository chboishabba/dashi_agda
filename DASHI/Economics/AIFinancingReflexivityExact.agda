module DASHI.Economics.AIFinancingReflexivityExact where

open import DASHI.Core.Prelude
import DASHI.Economics.ReflexiveFlowValidationExact as Econ

------------------------------------------------------------------------
-- AI-SPECIFIC SPECIALISATION OF GENERIC ECONOMIC REFLEXIVITY
--
-- No empirical claim that a named firm inhabits these receipts is made here.
-- Such promotion requires a source-backed application module.
------------------------------------------------------------------------

data AILayer : Set where
  frontierLab hyperscaler acceleratorVendor neocloud datacentre financier : AILayer

record AIInfrastructureFlowSystem : Set₁ where
  field
    economicSystem : Econ.EconomicFlowSystem
    layerOf : Econ.Entity economicSystem → AILayer

open AIInfrastructureFlowSystem public

record AICapitalRevenueReflexivity
    (sys : AIInfrastructureFlowSystem)
    (investor customer : Econ.Entity (economicSystem sys)) : Set where
  field
    cycle : Econ.CapitalToCustomerCycle (economicSystem sys) investor customer

record AIValuationReflexivity
    (sys : AIInfrastructureFlowSystem)
    (investor investee : Econ.Entity (economicSystem sys)) : Set where
  field
    reflexivity : Econ.ValuationReflexivity (economicSystem sys) investor investee

data AIFinancingReflexivityImpliesFraudPermission : Set where

aIFinancingReflexivityDoesNotAutoPromoteToFraud :
  AIFinancingReflexivityImpliesFraudPermission → ⊥
aIFinancingReflexivityDoesNotAutoPromoteToFraud ()

markedGainDoesNotCloseExternalCash :
  Econ.MarkedGainImpliesExternalCashPermission → ⊥
markedGainDoesNotCloseExternalCash = Econ.markedGainDoesNotAutoPromoteToExternalCash
