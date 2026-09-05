module DASHI.Culture.AmyEskridgeGravityMechanismCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ViewpointProvenanceBidiExact as V
import DASHI.Culture.MissingDeceasedViewpointEvidenceExact as EV
import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalHyperfabricExact as H
import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalBidiExact as B

------------------------------------------------------------------------
-- AMY ESKRIDGE x ENGINEERED INERTIAL-GRAVITATIONAL RESPONSE
--
-- This bridge preserves the distinction between:
--   * evidence of Eskridge's public viewpoint/research interest;
--   * historical mechanism families she discussed;
--   * the physical truth of those mechanism families.
-- No viewpoint receipt is promoted into a physics validation receipt.
------------------------------------------------------------------------

record ViewpointPhysicsBoundary : Set where
  constructor viewpoint-physics-boundary
  field
    eskridgeDiscussedExoticPropulsion : Bool
    eskridgeDiscussedExoticPropulsionIsTrue :
      eskridgeDiscussedExoticPropulsion ≡ true

    discussionProvesMechanism : Bool
    discussionProvesMechanismIsFalse : discussionProvesMechanism ≡ false

    suppressionBeliefProvesMechanism : Bool
    suppressionBeliefProvesMechanismIsFalse :
      suppressionBeliefProvesMechanism ≡ false

    publicDisclosureProvesMechanism : Bool
    publicDisclosureProvesMechanismIsFalse :
      publicDisclosureProvesMechanism ≡ false

canonicalViewpointPhysicsBoundary : ViewpointPhysicsBoundary
canonicalViewpointPhysicsBoundary =
  viewpoint-physics-boundary true refl false refl false refl false refl

------------------------------------------------------------------------
-- Same-person receipt reuse.  We point to the already-owned viewpoint receipt
-- rather than creating a second Amy Eskridge testimony/evidence object.
------------------------------------------------------------------------

amyExoticPropulsionReceipt : V.ViewpointReceipt
amyExoticPropulsionReceipt = EV.amySuppressedPropulsion

------------------------------------------------------------------------
-- Mechanism chart for the research programme discussed around Eskridge.
-- These are candidate-family coordinates, not claims that she uniquely owned
-- or experimentally established the underlying theories.
------------------------------------------------------------------------

record EskridgeMechanismChart : Set where
  constructor eskridge-mechanism-chart
  field
    coherentSuperconductorGravity : B.MechanismFamily
    superconductingWeightAnomaly : B.MechanismFamily
    impulsiveSuperconductorMomentum : B.MechanismFamily
    highVoltageMomentumAlternative : B.MechanismFamily
    machianInertialVariation : B.MechanismFamily
    negativeMassOrMetricLane : B.MechanismFamily

canonicalEskridgeMechanismChart : EskridgeMechanismChart
canonicalEskridgeMechanismChart = eskridge-mechanism-chart
  B.liTorrCoherentGravity
  B.podkletnovWeightAnomaly
  B.impulsiveSuperconductor
  B.electrohydrodynamicForce
  B.woodwardInertialVariation
  B.metricEngineering

------------------------------------------------------------------------
-- Cross-pollinated commonality.
--
-- The programme is represented as a search over engineered states whose
-- outputs may land in gravity, inertia, or momentum fibres.  Shared apparatus
-- motifs (coherence, high fields, rotation, time dependence) do not identify a
-- unique exotic coupling.
------------------------------------------------------------------------

record EskridgeCommonalityKernel : Set where
  constructor eskridge-commonality-kernel
  field
    engineeredNonGenericState : Bool
    engineeredNonGenericStateIsTrue :
      engineeredNonGenericState ≡ true

    searchesConstitutiveOrResponseResidual : Bool
    searchesConstitutiveOrResponseResidualIsTrue :
      searchesConstitutiveOrResponseResidual ≡ true

    sharedApparatusMotifDeterminesSharedMechanism : Bool
    sharedApparatusMotifDeterminesSharedMechanismIsFalse :
      sharedApparatusMotifDeterminesSharedMechanism ≡ false

    thrustAloneDiscriminatesGravityFromMomentum : Bool
    thrustAloneDiscriminatesGravityFromMomentumIsFalse :
      thrustAloneDiscriminatesGravityFromMomentum ≡ false

canonicalEskridgeCommonalityKernel : EskridgeCommonalityKernel
canonicalEskridgeCommonalityKernel =
  eskridge-commonality-kernel true refl true refl false refl false refl

------------------------------------------------------------------------
-- Experimental BIDI router for an Eskridge-style programme.
------------------------------------------------------------------------

record EskridgeExperimentalBidi : Set where
  constructor eskridge-experimental-bidi
  field
    claimedGravityEffectRoutesToFreeFall : Bool
    claimedGravityEffectRoutesToFreeFallIsTrue :
      claimedGravityEffectRoutesToFreeFall ≡ true

    claimedFieldEffectRoutesToRemoteTestMass : Bool
    claimedFieldEffectRoutesToRemoteTestMassIsTrue :
      claimedFieldEffectRoutesToRemoteTestMass ≡ true

    claimedCoherenceEffectRoutesToPhaseCrossing : Bool
    claimedCoherenceEffectRoutesToPhaseCrossingIsTrue :
      claimedCoherenceEffectRoutesToPhaseCrossing ≡ true

    claimedThrustRoutesToMomentumClosure : Bool
    claimedThrustRoutesToMomentumClosureIsTrue :
      claimedThrustRoutesToMomentumClosure ≡ true

    claimedIonWindExclusionRoutesToVacuumControl : Bool
    claimedIonWindExclusionRoutesToVacuumControlIsTrue :
      claimedIonWindExclusionRoutesToVacuumControl ≡ true

canonicalEskridgeExperimentalBidi : EskridgeExperimentalBidi
canonicalEskridgeExperimentalBidi =
  eskridge-experimental-bidi true refl true refl true refl true refl true refl

------------------------------------------------------------------------
-- Strong firewall inherited by cross-pollination.
------------------------------------------------------------------------

record EskridgeMechanismPromotionBoundary : Set where
  constructor eskridge-mechanism-promotion-boundary
  field
    historicalClaimPlusAnomalousForceClosesGravityMechanism : Bool
    historicalClaimPlusAnomalousForceClosesGravityMechanismIsFalse :
      historicalClaimPlusAnomalousForceClosesGravityMechanism ≡ false

    standardPhysicsResidualRequiredBeforeNewPhysicsPromotion : Bool
    standardPhysicsResidualRequiredBeforeNewPhysicsPromotionIsTrue :
      standardPhysicsResidualRequiredBeforeNewPhysicsPromotion ≡ true

    channelSpecificReceiptRequired : Bool
    channelSpecificReceiptRequiredIsTrue :
      channelSpecificReceiptRequired ≡ true

canonicalEskridgeMechanismPromotionBoundary : EskridgeMechanismPromotionBoundary
canonicalEskridgeMechanismPromotionBoundary =
  eskridge-mechanism-promotion-boundary false refl true refl true refl
