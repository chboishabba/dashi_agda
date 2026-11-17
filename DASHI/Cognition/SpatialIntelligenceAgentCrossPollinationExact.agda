module DASHI.Cognition.SpatialIntelligenceAgentCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.ProtectiveSpatialIntelligenceExact as Protective

------------------------------------------------------------------------
-- SPATIAL-REASONING AGENT CROSS-POLLINATION
--
-- Current Google Earth AI / Google Research work is used only as a public SOTA
-- precedent for the architecture:
--
--   upfront planning + domain-specific models + spatial tools -> analysis
--
-- This does not import Google product authority into VILYA or DASHI, and does
-- not turn model-generated spatial findings into protective or force authority.
------------------------------------------------------------------------

data SpatialReasoningSource : Set where
  googleEarthAIGeospatialReasoning20261014 : SpatialReasoningSource
  bilawalGodsEyeView2026 : SpatialReasoningSource
  vilyaProtectiveWorkflow2026 : SpatialReasoningSource

sourceLocator : SpatialReasoningSource → String
sourceLocator googleEarthAIGeospatialReasoning20261014 =
  "Google Research, 2026-10-14: geospatial reasoning agent combines upfront planning, domain-specific foundation models and spatial tools"
sourceLocator bilawalGodsEyeView2026 =
  "Bilawal Sidhu / Halfpixel God's Eye View: public/open spatial-intelligence world visualization"
sourceLocator vilyaProtectiveWorkflow2026 =
  "VILYA public workflow: site understanding, threat assessment, mission planning, live monitoring and briefing"

data SpatialToolKind : Set where
  worldModelTool : SpatialToolKind
  terrainAndBuildingTool : SpatialToolKind
  visibilityTool : SpatialToolKind
  coverageTool : SpatialToolKind
  routeTool : SpatialToolKind
  liveObservationTool : SpatialToolKind
  openSourceIntelTool : SpatialToolKind
  reportTool : SpatialToolKind

record SpatialReasoningQuery : Set where
  constructor spatial-reasoning-query
  field
    protectedConsumer : Protective.ProtectiveConsumer
    planReference : String
    selectedToolReference : String
    sourceStateReference : String
    outputFindingReference : String
    uncertaintyReference : String
    humanReviewReference : String

open SpatialReasoningQuery public

geospatialReasoningAgentPatternPaid : Bool
geospatialReasoningAgentPatternPaid = true

reasoningAgentCreatesProtectiveAuthority : Bool
reasoningAgentCreatesProtectiveAuthority = false

reasoningAgentCreatesUseOfForceAuthority : Bool
reasoningAgentCreatesUseOfForceAuthority = false

agentFindingEqualsDirectObservation : Bool
agentFindingEqualsDirectObservation = false

agentPlanCreatesSourceTruth : Bool
agentPlanCreatesSourceTruth = false

sharedAgentArchitectureProvesProductLineage : Bool
sharedAgentArchitectureProvesProductLineage = false

formerGoogleEmploymentProvesGoogleProductLineage : Bool
formerGoogleEmploymentProvesGoogleProductLineage = false

record SpatialReasoningAgentBoundary : Set where
  constructor spatial-reasoning-agent-boundary
  field
    planningToolCompositionIsReusablePattern : Bool
    derivedFindingNeedsProvenance : Bool
    derivedFindingIsDirectObservation : Bool
    modelOutputCreatesOperationalAuthority : Bool
    modelOutputCreatesForceAuthority : Bool
    sharedArchitectureCreatesInstitutionalLineage : Bool

canonicalSpatialReasoningAgentBoundary : SpatialReasoningAgentBoundary
canonicalSpatialReasoningAgentBoundary =
  spatial-reasoning-agent-boundary true true false false false false
