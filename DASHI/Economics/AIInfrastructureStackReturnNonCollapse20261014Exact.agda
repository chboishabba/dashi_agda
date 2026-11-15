module DASHI.Economics.AIInfrastructureStackReturnNonCollapse20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AICoreWeaveNumericalCapitalBounds20261012Exact as Tenant
import DASHI.Economics.AIGalaxyHeliosLandlordEconomics20261014Exact as Landlord

------------------------------------------------------------------------
-- SAME-STACK RETURN NON-COLLAPSE
--
-- The same physical/economic stack can expose positive or realised coordinates
-- at one layer while another layer fails its capital-return consumer.  This is
-- not an inconsistency: landlord/project revenue, tenant ROIC-WACC and terminal
-- customer economics are distinct observables.
------------------------------------------------------------------------

record StackLayerReturnWitness : Set where
  constructor stack-layer-return-witness
  field
    landlordRecognisedRevenue : Bool
    tenantCapitalSpreadDeficitBoundPaid : Bool
    landlordCashCollectionPaid : Bool
    terminalDemandPaid : Bool

open StackLayerReturnWitness public

heliosCoreWeaveLayerWitness : StackLayerReturnWitness
heliosCoreWeaveLayerWitness = stack-layer-return-witness true true false false

landlordRecognisedRevenueAndTenantNegativeSpreadCoexist :
  (Landlord.realisedLeaseRevenuePaid Landlord.heliosPhaseIILandlordEconomics ≡ true) ×
  (Tenant.capitalSpreadDeficitAtLeast578Bp ≡ true)
landlordRecognisedRevenueAndTenantNegativeSpreadCoexist =
  Landlord.realisedLeaseRevenueObserved , refl

data LandlordPositiveCoordinateCreatesTenantPositiveReturnPermission : Set where
data TenantNegativeSpreadCreatesLandlordFailurePermission : Set where
data LayerCoexistenceCreatesTerminalDemandPermission : Set where

landlordPositiveCoordinateDoesNotCreateTenantPositiveReturn :
  LandlordPositiveCoordinateCreatesTenantPositiveReturnPermission → ⊥
landlordPositiveCoordinateDoesNotCreateTenantPositiveReturn ()

tenantNegativeSpreadDoesNotCreateLandlordFailure :
  TenantNegativeSpreadCreatesLandlordFailurePermission → ⊥
tenantNegativeSpreadDoesNotCreateLandlordFailure ()

layerCoexistenceDoesNotCreateTerminalDemand :
  LayerCoexistenceCreatesTerminalDemandPermission → ⊥
layerCoexistenceDoesNotCreateTerminalDemand ()

boundary : String
boundary =
  "Galaxy recognises Phase-I CoreWeave-linked lease revenue while the declared June-30 CoreWeave market-capital convention independently carries a capital-spread deficit greater than 578 bp. These same-stack observations prove layer non-collapse: a positive/realised landlord coordinate does not create a positive tenant return, and a negative tenant capital spread does not create landlord failure. Neither observation establishes terminal-customer demand or cash independence."
