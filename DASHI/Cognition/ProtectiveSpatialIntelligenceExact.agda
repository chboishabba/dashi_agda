module DASHI.Cognition.ProtectiveSpatialIntelligenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as GEV

------------------------------------------------------------------------
-- PROTECTIVE SPATIAL INTELLIGENCE
--
-- This owner is a thin protective-operations consumer over the already-merged
-- God's Eye View proof-carrying world ontology.  It does not create another
-- world ontology and does not grant surveillance or intervention authority.
------------------------------------------------------------------------

data ProtectiveLayerKind : Set where
  terrainAndElevation : ProtectiveLayerKind
  buildingGeometry : ProtectiveLayerKind
  accessAndOwnership : ProtectiveLayerKind
  lineOfSight : ProtectiveLayerKind
  cameraCoverage : ProtectiveLayerKind
  routeAndZone : ProtectiveLayerKind
  weatherAndConditions : ProtectiveLayerKind
  liveTeamPosition : ProtectiveLayerKind
  openSourceIntelligence : ProtectiveLayerKind
  protectiveAssessment : ProtectiveLayerKind

data ProtectiveConsumer : Set where
  siteUnderstandingConsumer : ProtectiveConsumer
  threatAssessmentConsumer : ProtectiveConsumer
  missionPlanningConsumer : ProtectiveConsumer
  liveOperationsConsumer : ProtectiveConsumer
  briefingAndReviewConsumer : ProtectiveConsumer

record ProtectiveSpatialLayer : Set where
  constructor protective-spatial-layer
  field
    layerKind : ProtectiveLayerKind
    worldState : GEV.ResolvedWorldState
    provenanceReference : String
    temporalReference : String
    uncertaintyReference : String
    accessAuthorityReference : String

open ProtectiveSpatialLayer public

record ProtectiveDecisionDemand : Set where
  constructor protective-decision-demand
  field
    consumer : ProtectiveConsumer
    requiredGeometryReference : String
    requiredObservationReference : String
    requiredCoverageReference : String
    operationalConstraintReference : String
    humanAuthorityReference : String
    decisionReference : String

open ProtectiveDecisionDemand public

------------------------------------------------------------------------
-- GEV anti-panopticon reuse.
------------------------------------------------------------------------

antiPanopticonBoundaryAnchor : GEV.AntiPanopticonBoundary
antiPanopticonBoundaryAnchor = GEV.canonicalAntiPanopticonBoundary

observationCreatesProtectiveAuthority : Bool
observationCreatesProtectiveAuthority = false

renderedVisibilityCreatesOmniscience : Bool
renderedVisibilityCreatesOmniscience = false

moreSpatialLayersCreateInterventionAuthority : Bool
moreSpatialLayersCreateInterventionAuthority = false

uncoveredRegionMayBeDeclaredSafe : Bool
uncoveredRegionMayBeDeclaredSafe = false

provenanceMustSurviveProtectiveProjection : Bool
provenanceMustSurviveProtectiveProjection = true

------------------------------------------------------------------------
-- Consumer-relative sufficiency boundaries.
------------------------------------------------------------------------

mapGeometryAlonePaysProtectiveDecision : Bool
mapGeometryAlonePaysProtectiveDecision = false

cameraInventoryAlonePaysCoverageAdequacy : Bool
cameraInventoryAlonePaysCoverageAdequacy = false

lineOfSightLayerAlonePaysMitigation : Bool
lineOfSightLayerAlonePaysMitigation = false

protectiveDecisionRequiresHumanAuthority : Bool
protectiveDecisionRequiresHumanAuthority = true

record ProtectiveSpatialBoundary : Set where
  constructor protective-spatial-boundary
  field
    worldObservationRemainsEvidence : Bool
    protectionIsConsumerRelative : Bool
    observationIsAuthority : Bool
    visibilityIsOmniscience : Bool
    uncoveredMeansSafe : Bool
    provenanceRetained : Bool
    humanDecisionAuthorityRequired : Bool

canonicalProtectiveSpatialBoundary : ProtectiveSpatialBoundary
canonicalProtectiveSpatialBoundary =
  protective-spatial-boundary
    true true false false false true true
