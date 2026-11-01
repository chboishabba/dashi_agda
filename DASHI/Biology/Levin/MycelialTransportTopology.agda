module DASHI.Biology.Levin.MycelialTransportTopology where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.FungalNetworkAgencyBoundary as Fungal
import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy

------------------------------------------------------------------------
-- A mycelium is treated as a remodeling transport graph rather than as a
-- static wire diagram.  Topology, conductance, flux and growth all remain
-- empirically indexed and are not collapsed into a neural metaphor.

record MycelialGraphObservation : Set where
  field
    hyphalTipsObserved : Bool
    junctionsObserved : Bool
    connectionsObserved : Bool
    edgeConductanceEstimated : Bool
    resourceFluxMeasured : Bool
    pressureFluxMeasured : Bool
    electricalFluxMeasured : Bool
    topologyTrackedOverTime : Bool
    damageAndRepairTracked : Bool
    environmentalGradientsSpecified : Bool

record MycelialTransportTopologyBoundary : Set where
  field
    fungalBoundary : Fungal.FungalNetworkAgencyBoundary
    problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
    autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
    graphIsDynamicNotStatic : Bool
    growthAndTransportCoupled : Bool
    localFluxNotGlobalIntentByDefinition : Bool
    efficientTransportNotProofOfOptimality : Bool
    topologyChangeRequiresLongitudinalWitness : Bool
    resourceAllocationRequiresCompetingDemandWitness : Bool
    interpretation : String

canonicalMycelialTransportTopologyBoundary : MycelialTransportTopologyBoundary
canonicalMycelialTransportTopologyBoundary = record
  { fungalBoundary = Fungal.canonicalFungalNetworkAgencyBoundary
  ; problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary
  ; autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary
  ; graphIsDynamicNotStatic = true
  ; growthAndTransportCoupled = true
  ; localFluxNotGlobalIntentByDefinition = true
  ; efficientTransportNotProofOfOptimality = true
  ; topologyChangeRequiresLongitudinalWitness = true
  ; resourceAllocationRequiresCompetingDemandWitness = true
  ; interpretation = "Mycelial computation candidates are evaluated on a remodeling graph whose hyphal topology, conductance and chemical, hydraulic or electrical fluxes change with gradients, damage and competing demands; transport efficiency alone does not establish global intent"
  }
