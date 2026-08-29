module DASHI.PlanningArchitectureFractalValidation where

open import DASHI.Core.Prelude

import DASHI.Planning.PlanningSystemExact as Planning
import DASHI.Planning.PlanningRepresentationDescentExact as Descent
import DASHI.Architecture.SpatialRealisationExact as Spatial
import DASHI.Architecture.AgentRelativeAffordanceExact as Affordance
import DASHI.Architecture.PlanningArchitectureRealisationExact as Realisation
import DASHI.Planning.NestedSituatedPlanningExact as Nested
import DASHI.Planning.InhabitedLandscapeExact as Landscape
import DASHI.Architecture.SemiconductorBuiltEnvironmentCrossPollinationExact as Semiconductor
import DASHI.Planning.DataCentreUrbanResourceConflictExact as DataCentre
import DASHI.PlanningArchitectureSituatedCrossPollinationValidation as SituatedValidation
import DASHI.Planning.ConsentReparationPNFValidation as ConsentRepairValidation
import DASHI.Planning.ConsentReparationPNFBoundary as ConsentRepairBoundary
import DASHI.Planning.PlanningBIDICapstoneExact as BIDICapstone

------------------------------------------------------------------------
-- VALIDATION SURFACE
------------------------------------------------------------------------

planningStagesRemainDistinct : Planning.proposed ≡ Planning.approved → ⊥
planningStagesRemainDistinct = Planning.proposalIsNotApproval

coarsePlanningViewCanEraseArchitecturalProperty :
  Descent.planningProjection Descent.shadedCourtyard ≡
  Descent.planningProjection Descent.exposedCourtyard
coarsePlanningViewCanEraseArchitecturalProperty =
  Descent.samePlanningProjection

localPlacementStillDoesNotCloseGlobalRouting :
  Spatial.LocalValidityImpliesGlobalRoutabilityPermission → ⊥
localPlacementStillDoesNotCloseGlobalRouting =
  Spatial.localValidityDoesNotAutoPromoteToGlobalRoutability

geometryStillDoesNotCloseUsability :
  Affordance.AffordanceSystem.Affords Affordance.architectureAffordanceSystem
    Affordance.stairOnlyConnection Affordance.stepFreeUser
    Affordance.reachUpperLevel → ⊥
geometryStillDoesNotCloseUsability = Affordance.notUsableForOtherAgent

planningPermissionStillDoesNotClosePhysicalFeasibility :
  Realisation.PlanningArchitectureInterface.PhysicallyFeasible
    Realisation.interface Realisation.paperDesign → ⊥
planningPermissionStillDoesNotClosePhysicalFeasibility feasible = feasible

innerFeasibilityStillDoesNotCloseOuterFeasibility :
  Nested.Feasible Nested.outerSystem Nested.gridCommitted → ⊥
innerFeasibilityStillDoesNotCloseOuterFeasibility = Nested.outerFutureCanBeLost

ruralUrbanLandscapeRetainsMultifunctionality :
  Landscape.InhabitedLandscape.Role
      Landscape.landscape Landscape.marketGarden Landscape.home ×
  Landscape.InhabitedLandscape.Role
      Landscape.landscape Landscape.marketGarden Landscape.foodProduction
ruralUrbanLandscapeRetainsMultifunctionality = tt , tt

semiconductorCrossPollinationKeepsOutcomeBoundary :
  Semiconductor.RepresentationCorrectnessImpliesOutcomeSuccessPermission → ⊥
semiconductorCrossPollinationKeepsOutcomeBoundary =
  Semiconductor.representationCorrectnessDoesNotAutoPromoteToOutcomeSuccess

dataCentreSpatialSeparationDoesNotRemoveResourceCompetition :
  DataCentre.CompetesFor
    DataCentre.housingProject DataCentre.aiDataCentre DataCentre.electricity
dataCentreSpatialSeparationDoesNotRemoveResourceCompetition = tt , tt

consultationStillDoesNotCloseConsent :
  ConsentRepairBoundary.ConsentReparationPNFBoundary.consultationIsConsent
    ConsentRepairBoundary.canonicalConsentReparationPNFBoundary ≡ false
consultationStillDoesNotCloseConsent = refl

compensationStillDoesNotCloseAuthorityRepair :
  ConsentRepairBoundary.ConsentReparationPNFBoundary.compensationIsAuthorityRestoration
    ConsentRepairBoundary.canonicalConsentReparationPNFBoundary ≡ false
compensationStillDoesNotCloseAuthorityRepair = refl

rankedBIDICapstoneIsImported :
  BIDICapstone.Cases.CaseSource.freshness
    BIDICapstone.Cases.trumpIranPalestineLiveSourceBoundary ≡
  BIDICapstone.Cases.liveRefreshRequired
rankedBIDICapstoneIsImported = refl
