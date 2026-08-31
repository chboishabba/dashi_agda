module DASHI.Planning.AgenticMaterialProcessPlanningCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy
import DASHI.Governance.LevinAgenticMaterialRealisedTopologyCrossPollinationExact as Levin
import DASHI.Planning.PlanningAdmissibleTransitionBridgeExact as Admission
import DASHI.Planning.NetworkFlowCapacityCongestionExact as Network
import DASHI.Planning.ChemicalManufacturingInventoryLogisticsCrossPollinationExact as Chemical
import DASHI.Core.ObservationInterventionTrustFibreExact as Observation

------------------------------------------------------------------------
-- AGENTIC MATERIALS / PROCESS / LOGISTICS / PLANNING
--
-- Materials may be stateful, adaptive, self-maintaining, or recover after
-- perturbation.  Planning therefore cannot always model them as passive scalar
-- inventory.  But adaptive material behaviour is not itself consciousness,
-- intent, or permission to alter process constraints.
------------------------------------------------------------------------

data MaterialPlanningModel : Set where
  passiveScalarInventory
  statefulResponsiveInventory
  : MaterialPlanningModel

data ProcessResponse : Set where
  unchangedResponse adaptiveRecoveryResponse degradedResponse : ProcessResponse

data PlannerObservation : Set where
  nominalSpecOnly stateAndHistoryObserved : PlannerObservation

data ProcessAdmissibility : Set where
  processAdmitted processBlocked : ProcessAdmissibility

record StatefulMaterialPlanningState : Set where
  constructor stateful-material-planning-state
  field
    model : MaterialPlanningModel
    observation : PlannerObservation
    response : ProcessResponse
    admissibility : ProcessAdmissibility

open StatefulMaterialPlanningState public

coarsePlan : StatefulMaterialPlanningState
coarsePlan =
  stateful-material-planning-state passiveScalarInventory nominalSpecOnly
    unchangedResponse processAdmitted

historySensitivePlan : StatefulMaterialPlanningState
historySensitivePlan =
  stateful-material-planning-state statefulResponsiveInventory stateAndHistoryObserved
    degradedResponse processBlocked

------------------------------------------------------------------------
-- Same nominal specification may hide different process futures.
------------------------------------------------------------------------

data NominalMaterialSpec : Set where sameNominalSpec : NominalMaterialSpec

nominalSpec : StatefulMaterialPlanningState → NominalMaterialSpec
nominalSpec _ = sameNominalSpec

sameNominalSpecification : nominalSpec coarsePlan ≡ nominalSpec historySensitivePlan
sameNominalSpecification = refl

processAdmissibilityDiffers :
  admissibility coarsePlan ≡ admissibility historySensitivePlan → ⊥
processAdmissibilityDiffers ()

------------------------------------------------------------------------
-- Process application receipt for adaptive/stateful material behaviour.
------------------------------------------------------------------------

record AgenticMaterialProcessReceipt : Set where
  constructor agentic-material-process-receipt
  field
    materialIdentityReference : String
    physicalStateReference : String
    relevantHistoryReference : String
    problemSpaceReference : String
    perturbationReference : String
    responseOrRecoveryReference : String
    constitutiveBoundaryReference : String
    processCompatibilityReference : String
    safetyEnvelopeReference : String
    processYieldReference : String
    inventoryCustodyReference : String
    monitoringReference : String
    validationReference : String

------------------------------------------------------------------------
-- Imported owners.
------------------------------------------------------------------------

levinBoundary : Levin.LevinAgenticMaterialRealisedTopologyBoundary
levinBoundary = Levin.canonicalLevinAgenticMaterialRealisedTopologyBoundary

problemBoundary : Problem.ProblemSpaceAgencyBoundary
problemBoundary = Problem.canonicalProblemSpaceAgencyBoundary

autonomyBoundary : Autonomy.ConstitutiveInteractiveAutonomyBoundary
autonomyBoundary = Autonomy.canonicalConstitutiveInteractiveAutonomyBoundary

planningBoundary : Admission.PlanningAdmissibleTransitionBoundary
planningBoundary = Admission.canonicalPlanningAdmissibleTransitionBoundary

networkBoundary : Network.CoupledNetworkBoundary
networkBoundary = Network.canonicalCoupledNetworkBoundary

chemicalBoundary : Chemical.ChemicalManufacturingInventoryLogisticsBoundary
chemicalBoundary = Chemical.canonicalChemicalManufacturingInventoryLogisticsBoundary

observationBoundary : Observation.ObservationInterventionTrustBoundary
observationBoundary = Observation.canonicalObservationInterventionTrustBoundary

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record AgenticMaterialProcessPlanningBoundary : Set where
  constructor agentic-material-process-planning-boundary
  field
    nominalSpecDeterminesCurrentMaterialState : Bool
    nominalSpecDeterminesCurrentMaterialStateIsFalse :
      nominalSpecDeterminesCurrentMaterialState ≡ false
    nominalSpecDeterminesFutureProcessResponse : Bool
    nominalSpecDeterminesFutureProcessResponseIsFalse :
      nominalSpecDeterminesFutureProcessResponse ≡ false
    adaptiveResponseImpliesConsciousness : Bool
    adaptiveResponseImpliesConsciousnessIsFalse :
      adaptiveResponseImpliesConsciousness ≡ false
    materialAgencyOverridesPlantSafetyEnvelope : Bool
    materialAgencyOverridesPlantSafetyEnvelopeIsFalse :
      materialAgencyOverridesPlantSafetyEnvelope ≡ false
    plannedInventoryDeterminesPhysicalResponsiveState : Bool
    plannedInventoryDeterminesPhysicalResponsiveStateIsFalse :
      plannedInventoryDeterminesPhysicalResponsiveState ≡ false
    localAdaptiveCompetencyImpliesWholeNetworkFeasibility : Bool
    localAdaptiveCompetencyImpliesWholeNetworkFeasibilityIsFalse :
      localAdaptiveCompetencyImpliesWholeNetworkFeasibility ≡ false
    processPlanningNeedsStateHistoryAndInterventionReceipts : Bool
    processPlanningNeedsStateHistoryAndInterventionReceiptsIsTrue :
      processPlanningNeedsStateHistoryAndInterventionReceipts ≡ true
    reading : String

canonicalAgenticMaterialProcessPlanningBoundary : AgenticMaterialProcessPlanningBoundary
canonicalAgenticMaterialProcessPlanningBoundary =
  agentic-material-process-planning-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    "Stateful or agentic-material behaviour makes material state and history planning-relevant: nominal specification and allocated inventory need not determine actual process response. Adaptive recovery is evidence about competency in an explicit problem space, not consciousness or authority to violate plant safety. Local material competency also does not establish whole-network feasibility."
