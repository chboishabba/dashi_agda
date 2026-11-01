module DASHI.Biology.Levin.NicheConstructionProblemSpace where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy
import DASHI.Biology.Levin.MycelialTransportTopology as Topology

record NicheConstructionObservation : Set where
  field
    agentStateTracked : Bool
    environmentStateTracked : Bool
    environmentalModificationMeasured : Bool
    laterActionSetChanged : Bool
    laterFitnessConsequencesMeasured : Bool
    persistenceAfterAgentDepartureMeasured : Bool
    beneficiarySetSpecified : Bool
    collateralCostsMeasured : Bool

record NicheConstructionBoundary : Set where
  field
    problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
    autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
    topologyBoundary : Topology.MycelialTransportTopologyBoundary
    agentMayModifyProblemSpace : Bool
    environmentMayStoreExternalState : Bool
    environmentalPersistenceNotInternalMemory : Bool
    habitatImprovementNotAltruismByDefinition : Bool
    pollutantTransformationNotGeneralRemediationProof : Bool
    futureAffordanceChangeRequiresLongitudinalWitness : Bool
    interpretation : String

canonicalNicheConstructionBoundary : NicheConstructionBoundary
canonicalNicheConstructionBoundary = record
  { problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary
  ; autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary
  ; topologyBoundary = Topology.canonicalMycelialTransportTopologyBoundary
  ; agentMayModifyProblemSpace = true
  ; environmentMayStoreExternalState = true
  ; environmentalPersistenceNotInternalMemory = true
  ; habitatImprovementNotAltruismByDefinition = true
  ; pollutantTransformationNotGeneralRemediationProof = true
  ; futureAffordanceChangeRequiresLongitudinalWitness = true
  ; interpretation = "Fungi and other organisms may change the topology, chemistry and affordances of the problem space they later navigate; durable environmental traces remain distinct from internal memory and beneficial niche construction is not altruism by definition"
  }
