module DASHI.Biology.ResourceCoupledMetabolicAdmissibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Biology.ResourceCoupledLogisticReplicationExact as Resource
import DASHI.Biology.ResourceCoupledMetabolicOpenBalanceBridgeExact as Balance
import DASHI.Biology.Cell.OpenMetabolicNetwork as OMN
import DASHI.Biology.Cell.MetabolicStoichiometricConservation as MSC
import DASHI.Biology.Cell.MetabolicOpenSystemBalance as MOB
import DASHI.Biology.AgenticMaterialsControlCore as Agentic

------------------------------------------------------------------------
-- RESOURCE-COUPLED METABOLIC ADMISSIBILITY
--
-- Exact open-system balance is necessary bookkeeping, but the repository's
-- metabolic admissibility notion is stronger: a nontrivial cycle must dissipate
-- an environmental gradient while the internal state remains bounded and is
-- restoring.  This module aligns that stronger receipt with the same resource
-- realization used by the coupled logistic/open-balance bridge.
------------------------------------------------------------------------

record ResourceMetabolicAdmissibilityRealisation
    (S : Resource.ResourceCoupledLogisticSystem)
    (N : OMN.OpenMetabolicNetwork)
    (Sto : MSC.MetabolicStoichiometricBridge N)
    (B : MOB.MetabolicOpenBalanceBridge N Sto)
    (R : Balance.ResourceMetabolicOpenBalanceRealisation S N Sto B) : Set₁ where
  constructor resource-metabolic-admissibility-realisation
  field
    resource : Resource.Resource S

    admissibility : OMN.MetabolismAdmissibility N

    resourceStateMatches :
      Resource.resourceToNetworkState
        (Balance.metabolicResourceRealisation R)
        resource
      ≡ OMN.MetabolismAdmissibility.state admissibility

    resourceEnvironmentMatches :
      Resource.resourceToEnvironment
        (Balance.metabolicResourceRealisation R)
        resource
      ≡ OMN.MetabolismAdmissibility.environment admissibility

    admissibilityReference : String
    stateRealisationReference : String

open ResourceMetabolicAdmissibilityRealisation public

------------------------------------------------------------------------
-- Inherited metabolic witnesses.  Nothing here redefines metabolism.
------------------------------------------------------------------------

resourceHasNontrivialMetabolicCycle :
  ∀ {S N Sto B R} →
  (A : ResourceMetabolicAdmissibilityRealisation S N Sto B R) →
  OMN.OpenMetabolicNetwork.NontrivialCycle N
    (OMN.MetabolismAdmissibility.generatingCycle (admissibility A))
resourceHasNontrivialMetabolicCycle A =
  OMN.MetabolismAdmissibility.nontrivial (admissibility A)

resourceCycleDissipatesGradient :
  ∀ {S N Sto B R} →
  (A : ResourceMetabolicAdmissibilityRealisation S N Sto B R) →
  OMN.OpenMetabolicNetwork.DissipatesGradient N
    (OMN.MetabolismAdmissibility.environment (admissibility A))
    (OMN.MetabolismAdmissibility.generatingCycle (admissibility A))
    (OMN.MetabolismAdmissibility.state (admissibility A))
resourceCycleDissipatesGradient A =
  OMN.MetabolismAdmissibility.dissipative (admissibility A)

resourceMetabolicStateIsBounded :
  ∀ {S N Sto B R} →
  (A : ResourceMetabolicAdmissibilityRealisation S N Sto B R) →
  OMN.OpenMetabolicNetwork.BoundedInternalState N
    (OMN.MetabolismAdmissibility.state (admissibility A))
resourceMetabolicStateIsBounded A =
  OMN.MetabolismAdmissibility.bounded (admissibility A)

resourceMetabolicCycleIsRestoring :
  ∀ {S N Sto B R} →
  (A : ResourceMetabolicAdmissibilityRealisation S N Sto B R) →
  OMN.OpenMetabolicNetwork.Restoring N
    (OMN.MetabolismAdmissibility.environment (admissibility A))
    (OMN.MetabolismAdmissibility.generatingCycle (admissibility A))
    (OMN.MetabolismAdmissibility.state (admissibility A))
resourceMetabolicCycleIsRestoring A =
  OMN.MetabolismAdmissibility.restoring (admissibility A)

------------------------------------------------------------------------
-- Dynamic preservation is a separate receipt.  One admissible resource state
-- does not imply that every subsequent resource update remains admissible.
------------------------------------------------------------------------

record ResourceMetabolicAdmissibilityStep
    {S N Sto B}
    (R : Balance.ResourceMetabolicOpenBalanceRealisation S N Sto B)
    (population : Resource.Population S)
    (before : ResourceMetabolicAdmissibilityRealisation S N Sto B R) : Set₁ where
  constructor resource-metabolic-admissibility-step
  field
    after : OMN.MetabolismAdmissibility N

    afterStateMatches :
      Resource.resourceToNetworkState
        (Balance.metabolicResourceRealisation R)
        (Resource.resourceStep S population (resource before))
      ≡ OMN.MetabolismAdmissibility.state after

    afterEnvironmentMatches :
      Resource.resourceToEnvironment
        (Balance.metabolicResourceRealisation R)
        (Resource.resourceStep S population (resource before))
      ≡ OMN.MetabolismAdmissibility.environment after

    preservationReference : String

open ResourceMetabolicAdmissibilityStep public

------------------------------------------------------------------------
-- Agency remains a stronger, differently typed coordinate.
------------------------------------------------------------------------

data MetabolicAdmissibilityMeansAgencyPermission : Set where

data MetabolicAdmissibilityMeansHeredityPermission : Set where

data MetabolicAdmissibilityMeansAbiogenesisPermission : Set where

data OneAdmissibleStateMeansInvariantAdmissibilityPermission : Set where

metabolicAdmissibilityDoesNotByItselfProveAgency :
  MetabolicAdmissibilityMeansAgencyPermission → ⊥
metabolicAdmissibilityDoesNotByItselfProveAgency ()

metabolicAdmissibilityDoesNotByItselfProveHeredity :
  MetabolicAdmissibilityMeansHeredityPermission → ⊥
metabolicAdmissibilityDoesNotByItselfProveHeredity ()

metabolicAdmissibilityDoesNotByItselfProveAbiogenesis :
  MetabolicAdmissibilityMeansAbiogenesisPermission → ⊥
metabolicAdmissibilityDoesNotByItselfProveAbiogenesis ()

oneAdmissibleStateDoesNotProveDynamicPreservation :
  OneAdmissibleStateMeansInvariantAdmissibilityPermission → ⊥
oneAdmissibleStateDoesNotProveDynamicPreservation ()

record ResourceMetabolicAdmissibilityBoundary : Set where
  constructor resource-metabolic-admissibility-boundary
  field
    openBalanceAndMetabolicAdmissibilityAreDistinct : Bool
    nontrivialCycleRequired : Bool
    gradientDissipationRequired : Bool
    boundedInternalStateRequired : Bool
    restorationRequired : Bool
    dynamicPreservationRequiresSeparateReceipt : Bool
    metabolicAdmissibilityAutomaticallyCreatesAgency : Bool
    metabolicAdmissibilityAutomaticallyProvesAbiogenesis : Bool

canonicalResourceMetabolicAdmissibilityBoundary :
  ResourceMetabolicAdmissibilityBoundary
canonicalResourceMetabolicAdmissibilityBoundary =
  resource-metabolic-admissibility-boundary
    true true true true true true false false
