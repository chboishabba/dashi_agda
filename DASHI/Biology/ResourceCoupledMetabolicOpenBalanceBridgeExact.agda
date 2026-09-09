module DASHI.Biology.ResourceCoupledMetabolicOpenBalanceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)

import DASHI.Analysis.OpenSystemBalance as OSB
import DASHI.Analysis.StoichiometricConservation as SC
import DASHI.Biology.ResourceCoupledLogisticReplicationExact as Resource
import DASHI.Biology.Cell.OpenMetabolicNetwork as OMN
import DASHI.Biology.Cell.MetabolicStoichiometricConservation as MSC
import DASHI.Biology.Cell.MetabolicOpenSystemBalance as MOB
import DASHI.Biology.AgenticMaterialsControlCore as Agentic

------------------------------------------------------------------------
-- RESOURCE-COUPLED LOGISTIC / METABOLIC OPEN-BALANCE BRIDGE
--
-- The resource update F(N,R) becomes chemically accountable only when an
-- explicit ordered reaction/exchange path realises that update inside the
-- existing metabolic open-balance system.  No new balance algebra is created.
------------------------------------------------------------------------

record ResourceMetabolicOpenBalanceRealisation
    (S : Resource.ResourceCoupledLogisticSystem)
    (N : OMN.OpenMetabolicNetwork)
    (Sto : MSC.MetabolicStoichiometricBridge N)
    (B : MOB.MetabolicOpenBalanceBridge N Sto) : Set₁ where
  constructor resource-metabolic-open-balance-realisation
  field
    metabolicResourceRealisation :
      Resource.MetabolicResourceRealisation S N

    balancePath :
      Resource.Population S →
      Resource.Resource S →
      List
        (MOB.MetabolicBalanceEvent
          (OMN.OpenMetabolicNetwork.Reaction N)
          (MOB.Exchange B))

    pathRealisesResourceUpdate :
      (population : Resource.Population S) →
      (resource : Resource.Resource S) →
      OSB.runBalancePath
        (MOB.metabolicOpenBalanceSystem B)
        (balancePath population resource)
        (Resource.resourceToNetworkState
          metabolicResourceRealisation resource)
      ≡
      Resource.resourceToNetworkState
        metabolicResourceRealisation
        (Resource.resourceStep S population resource)

    resourcePathReference : String
    chemicalBalanceReference : String

open ResourceMetabolicOpenBalanceRealisation public

------------------------------------------------------------------------
-- Exact transfer of the existing path-balance theorem onto F(N,R).
------------------------------------------------------------------------

resourceUpdateQuantityBalance :
  ∀ {S N Sto B} →
  (R : ResourceMetabolicOpenBalanceRealisation S N Sto B) →
  (population : Resource.Population S) →
  (resource : Resource.Resource S) →
  SC.quantity (MSC.stoichiometry Sto)
    (Resource.resourceToNetworkState
      (metabolicResourceRealisation R)
      (Resource.resourceStep S population resource))
  ≡
  SC._⊕_ (SC.additive (MSC.stoichiometry Sto))
    (SC.quantity (MSC.stoichiometry Sto)
      (Resource.resourceToNetworkState
        (metabolicResourceRealisation R)
        resource))
    (OSB.accumulatedIncrement
      (MOB.metabolicOpenBalanceSystem B)
      (balancePath R population resource)
      (Resource.resourceToNetworkState
        (metabolicResourceRealisation R)
        resource))
resourceUpdateQuantityBalance {Sto = Sto} {B = B} R population resource =
  trans
    (cong
      (SC.quantity (MSC.stoichiometry Sto))
      (sym (pathRealisesResourceUpdate R population resource)))
    (OSB.pathBalance
      (MOB.metabolicOpenBalanceSystem B)
      (balancePath R population resource)
      (Resource.resourceToNetworkState
        (metabolicResourceRealisation R)
        resource))

------------------------------------------------------------------------
-- The generic open-balance certificate is inherited, not reproved.
------------------------------------------------------------------------

resourceBalanceCertificate :
  ∀ {S N Sto B} →
  (R : ResourceMetabolicOpenBalanceRealisation S N Sto B) →
  MOB.MetabolicOpenBalanceCertificate B
resourceBalanceCertificate R =
  MOB.certifyMetabolicOpenBalance _

------------------------------------------------------------------------
-- Product-step receipt: population growth and chemical resource accounting
-- are two projections of one coupled state transition, but only the resource
-- projection is discharged by the open-balance theorem here.
------------------------------------------------------------------------

record ResourceCoupledMetabolicStepReceipt
    {S N Sto B}
    (R : ResourceMetabolicOpenBalanceRealisation S N Sto B)
    (before : Resource.ResourcePopulationState S) : Set₁ where
  constructor resource-coupled-metabolic-step-receipt
  field
    coupledReceipt :
      Resource.ResourceCoupledStepReceipt S before
        (Resource.coupledStep S before)

    chemicalBalance :
      SC.quantity (MSC.stoichiometry Sto)
        (Resource.resourceToNetworkState
          (metabolicResourceRealisation R)
          (Resource.resource
            (Resource.coupledStep S before)))
      ≡
      SC._⊕_ (SC.additive (MSC.stoichiometry Sto))
        (SC.quantity (MSC.stoichiometry Sto)
          (Resource.resourceToNetworkState
            (metabolicResourceRealisation R)
            (Resource.resource before)))
        (OSB.accumulatedIncrement
          (MOB.metabolicOpenBalanceSystem B)
          (balancePath R
            (Resource.population before)
            (Resource.resource before))
          (Resource.resourceToNetworkState
            (metabolicResourceRealisation R)
            (Resource.resource before)))

open ResourceCoupledMetabolicStepReceipt public

canonicalResourceCoupledMetabolicStepReceipt :
  ∀ {S N Sto B} →
  (R : ResourceMetabolicOpenBalanceRealisation S N Sto B) →
  (before : Resource.ResourcePopulationState S) →
  ResourceCoupledMetabolicStepReceipt R before
canonicalResourceCoupledMetabolicStepReceipt {S = S} R before =
  resource-coupled-metabolic-step-receipt
    (Resource.canonicalResourceCoupledStepReceipt S before)
    (resourceUpdateQuantityBalance R
      (Resource.population before)
      (Resource.resource before))

------------------------------------------------------------------------
-- Authority firewalls.
------------------------------------------------------------------------

data OpenBalanceRealisationMeansMetabolicAdmissibilityPermission : Set where

data OpenBalanceRealisationMeansAgencyPermission : Set where

data OpenBalanceRealisationMeansAbiogenesisPermission : Set where

data BalancedResourcePathMeansUniqueHistoricalPathPermission : Set where

openBalanceDoesNotByItselfProveMetabolicAdmissibility :
  OpenBalanceRealisationMeansMetabolicAdmissibilityPermission → ⊥
openBalanceDoesNotByItselfProveMetabolicAdmissibility ()

openBalanceDoesNotByItselfProveAgency :
  OpenBalanceRealisationMeansAgencyPermission → ⊥
openBalanceDoesNotByItselfProveAgency ()

openBalanceDoesNotByItselfProveAbiogenesis :
  OpenBalanceRealisationMeansAbiogenesisPermission → ⊥
openBalanceDoesNotByItselfProveAbiogenesis ()

balancedResourcePathDoesNotProveUniqueHistory :
  BalancedResourcePathMeansUniqueHistoricalPathPermission → ⊥
balancedResourcePathDoesNotProveUniqueHistory ()

record ResourceMetabolicBalanceBoundary : Set where
  constructor resource-metabolic-balance-boundary
  field
    resourceUpdateMayBeRealisedByChemicalEventPath : Bool
    resourceQuantityMayInheritExactOpenBalance : Bool
    populationAndChemicalCoordinatesRemainDistinct : Bool
    openBalanceAutomaticallySuppliesMetabolicAdmissibility : Bool
    openBalanceAutomaticallySuppliesAgency : Bool
    openBalanceAutomaticallyProvesAbiogenesis : Bool
    balancedPathAutomaticallyProvesUniqueHistory : Bool

canonicalResourceMetabolicBalanceBoundary : ResourceMetabolicBalanceBoundary
canonicalResourceMetabolicBalanceBoundary =
  resource-metabolic-balance-boundary
    true true true false false false false
