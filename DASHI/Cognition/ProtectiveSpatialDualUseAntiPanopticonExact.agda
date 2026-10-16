module DASHI.Cognition.ProtectiveSpatialDualUseAntiPanopticonExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.ProtectiveSpatialIntelligenceExact as Core
import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as GEV

------------------------------------------------------------------------
-- DUAL-USE / ANTI-PANOPTICON BOUNDARY
--
-- Spatial perception primitives may be shared by benign observation,
-- protective planning, targeting support and autonomous weapon systems.
-- Shared geometry/sensing does not determine purpose, authority or action.
--
-- Slaughterbots is retained as an advocacy/scenario source illustrating the
-- offensive autonomous-targeting failure mode; it is not treated as evidence
-- that a particular real system has those capabilities.
--
-- Current ICRC policy is retained as legal/humanitarian source authority for
-- the distinction between decision support and autonomous target selection /
-- application of force without further human intervention.
------------------------------------------------------------------------

data SpatialPurpose : Set where
  publicWorldObservation : SpatialPurpose
  protectivePlanning : SpatialPurpose
  protectiveDecisionSupport : SpatialPurpose
  targetingDecisionSupport : SpatialPurpose
  autonomousTargetSelectionAndForce : SpatialPurpose

data DualUseSource : Set where
  godsEyeViewUpstream : DualUseSource
  slaughterbotsFLI2017 : DualUseSource
  icrcAWSPosition2026 : DualUseSource

sourceLocator : DualUseSource → String
sourceLocator godsEyeViewUpstream =
  "Bilawal Sidhu God's Eye View: open spatial-intelligence visualization; safety-critical use explicitly disclaimed upstream"
sourceLocator slaughterbotsFLI2017 =
  "Future of Life Institute / Stuart Russell, Slaughterbots (2017): advocacy scenario about scalable autonomous anti-personnel targeting"
sourceLocator icrcAWSPosition2026 =
  "ICRC autonomous weapon systems FAQ/position, 2026: AWS select/apply force without further human intervention; preserve human control over life-and-death decisions"

record SpatialPurposeBinding : Set where
  constructor spatial-purpose-binding
  field
    purpose : SpatialPurpose
    observationReference : String
    declaredConsumerReference : String
    operatorAuthorityReference : String
    actionAuthorityReference : String
    auditReference : String

open SpatialPurposeBinding public

------------------------------------------------------------------------
-- Shared-primitives non-collapse.
------------------------------------------------------------------------

sameSpatialPrimitiveDeterminesProtectiveOrLethalPurpose : Bool
sameSpatialPrimitiveDeterminesProtectiveOrLethalPurpose = false

sameSightlineComputationCreatesSameOperationalMeaning : Bool
sameSightlineComputationCreatesSameOperationalMeaning = false

sameTrackingLayerCreatesSameAuthority : Bool
sameTrackingLayerCreatesSameAuthority = false

protectiveObservationCreatesAutonomousUseOfForceAuthority : Bool
protectiveObservationCreatesAutonomousUseOfForceAuthority = false

threatClassificationCreatesTargetingAuthority : Bool
threatClassificationCreatesTargetingAuthority = false

humanControlOverLifeDeathDecisionRequired : Bool
humanControlOverLifeDeathDecisionRequired = true

------------------------------------------------------------------------
-- Anti-panopticon anchors.
------------------------------------------------------------------------

antiPanopticonAnchor : GEV.AntiPanopticonBoundary
antiPanopticonAnchor = GEV.canonicalAntiPanopticonBoundary

protectivePurposeCancelsPrivacyInterest : Bool
protectivePurposeCancelsPrivacyInterest = false

securityPurposeCreatesUnlimitedCollectionAuthority : Bool
securityPurposeCreatesUnlimitedCollectionAuthority = false

moreCoverageCreatesOmniscience : Bool
moreCoverageCreatesOmniscience = false

------------------------------------------------------------------------
-- Defensive/offensive cut.
------------------------------------------------------------------------

record ProtectiveUseOfForceBoundary : Set where
  constructor protective-use-of-force-boundary
  field
    spatialObservationCanSupportProtection : Bool
    spatialObservationCanSupportHumanDecision : Bool
    observationAloneCreatesTargetAuthority : Bool
    consumerPurposeMustBeExplicit : Bool
    humanAuthorityMustRemainExplicit : Bool
    privacyAndNonDominationRemainLive : Bool
    autonomousAntiPersonnelPromotionAllowed : Bool

canonicalProtectiveUseOfForceBoundary : ProtectiveUseOfForceBoundary
canonicalProtectiveUseOfForceBoundary =
  protective-use-of-force-boundary
    true true false true true true false
