module DASHI.Economics.AICounterpartyRoleOverlap2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICompanyReturnRolloverTrajectory2026Exact as Company

------------------------------------------------------------------------
-- COUNTERPARTY ROLE OVERLAP
--
-- Ordinary customer concentration and economic independence are different.
-- A counterparty can be customer + lender, or customer + investor + partner.
-- This module records source-backed role overlap without promoting it to fraud,
-- circular revenue, lack of terminal demand, antitrust liability or capture.
------------------------------------------------------------------------

data EconomicRole : Set where
  customer lender investor supplier vendor partner researchCollaborator relatedParty : EconomicRole

record CounterpartyRoleReceipt : Set where
  constructor counterpartyRoleReceipt
  field
    counterparty : String
    disclosedRevenueShareBp : Nat
    roleCount : Nat
    roleReceipt : String
    source : Source.AttributedSource
    multiRole : Bool

open CounterpartyRoleReceipt public

mbzuaiCerebrasRoles : CounterpartyRoleReceipt
mbzuaiCerebrasRoles = counterpartyRoleReceipt
  "MBZUAI" 4900 4
  "H1-2026 revenue customer; Cerebras 2026 filing describes G42/MBZUAI relationships across customer/vendor/partner/research-collaborator roles and related-party context"
  Company.cerebrasQ22026Source true

g42CerebrasRoles : CounterpartyRoleReceipt
g42CerebrasRoles = counterpartyRoleReceipt
  "G42" 1000 4
  "H1-2026 revenue customer; separate Cerebras filing describes G42 as partner, customer and investor, with additional vendor/strategic relationship disclosures"
  Company.cerebrasQ22026Source true

openAICerebrasRoles : CounterpartyRoleReceipt
openAICerebrasRoles = counterpartyRoleReceipt
  "OpenAI" 1992 3
  "approximately 19.9 percent of H1-2026 revenue recognized under OpenAI arrangement; OpenAI also provided the approximately USD 1.0 billion working-capital loan and is a strategic capacity customer"
  Company.cerebrasQ22026Source true

record RoleOverlapRevenueBound : Set where
  constructor roleOverlapRevenueBound
  field
    company : String
    namedMultiRoleRevenueLowerBoundBp : Nat
    totalRevenueCoveredExactly : Bool
    terminalIndependenceEstablished : Bool
    circularRevenueEstablished : Bool

open RoleOverlapRevenueBound public

cerebrasNamedRoleOverlapLowerBound : RoleOverlapRevenueBound
cerebrasNamedRoleOverlapLowerBound = roleOverlapRevenueBound
  "Cerebras" 7892 false false false

------------------------------------------------------------------------
-- Raw concentration may improve while role-overlap dependence stays material.
------------------------------------------------------------------------

record ConcentrationIndependenceSeparation : Set where
  constructor concentrationIndependenceSeparation
  field
    company : String
    realisedHHILowerFell : Bool
    realisedHHIUpperFell : Bool
    namedRoleOverlapRevenueMaterial : Bool
    lowerHHIImpliesIndependentRevenue : Bool

open ConcentrationIndependenceSeparation public

cerebrasConcentrationVsIndependence : ConcentrationIndependenceSeparation
cerebrasConcentrationVsIndependence = concentrationIndependenceSeparation
  "Cerebras" true true true false

data MultiRoleCounterpartyImpliesCircularRevenuePermission : Set where
data LowerHHIImpliesTerminalIndependencePermission : Set where
data CustomerLenderOverlapImpliesFraudPermission : Set where

data CustomerInvestorOverlapImpliesAntitrustViolationPermission : Set where

multiRoleCounterpartyDoesNotAutoProveCircularRevenue :
  MultiRoleCounterpartyImpliesCircularRevenuePermission → ⊥
multiRoleCounterpartyDoesNotAutoProveCircularRevenue ()

lowerHHIDoesNotAutoProveTerminalIndependence :
  LowerHHIImpliesTerminalIndependencePermission → ⊥
lowerHHIDoesNotAutoProveTerminalIndependence ()

customerLenderOverlapDoesNotAutoProveFraud :
  CustomerLenderOverlapImpliesFraudPermission → ⊥
customerLenderOverlapDoesNotAutoProveFraud ()

customerInvestorOverlapDoesNotAutoProveAntitrustViolation :
  CustomerInvestorOverlapImpliesAntitrustViolationPermission → ⊥
customerInvestorOverlapDoesNotAutoProveAntitrustViolation ()

cerebrasRoleOverlapLowerBoundIs7892bp :
  namedMultiRoleRevenueLowerBoundBp cerebrasNamedRoleOverlapLowerBound ≡ 7892
cerebrasRoleOverlapLowerBoundIs7892bp = refl

cerebrasLowerHHIDoesNotCloseIndependence :
  lowerHHIImpliesIndependentRevenue cerebrasConcentrationVsIndependence ≡ false
cerebrasLowerHHIDoesNotCloseIndependence = refl
