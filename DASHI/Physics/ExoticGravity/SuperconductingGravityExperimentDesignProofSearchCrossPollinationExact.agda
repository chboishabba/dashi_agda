module DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentDesignProofSearchCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Core.ExperimentalCoordinateDesignExact as Coordinate
import DASHI.Core.DiscriminatorSynthesisExact as Disc
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Choice
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Core.ActiveBidiDiscriminatorLoopExact as Loop
import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as Split
import DASHI.Physics.ExoticGravity.SuperconductingSourceConstitutiveEvidenceBidiExact as Evidence

------------------------------------------------------------------------
-- SUPERCONDUCTING-GRAVITY EXPERIMENT DESIGN x REPOSITORY-NATIVE PROOF SEARCH
--
-- This owner does not invent a new experiment-planning language.  It maps the
-- source-vs-constitutive problem into the existing DASHI coordinate-design,
-- discriminator-synthesis, sequential-planning, actionability and active-BIDI
-- machinery.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Live hypothesis worlds.
------------------------------------------------------------------------

data HypothesisWorld : Set where
  sourceOnlyWorld
  constitutiveExcessWorld
  geometryArtifactWorld
  backgroundArtifactWorld
  nullWorld
  : HypothesisWorld

-- The coarse observer records only whether a phase-correlated external signal
-- exists.  Source-only and constitutive-excess worlds collide here.
coarseSignalObserver : HypothesisWorld → Bool
coarseSignalObserver sourceOnlyWorld = true
coarseSignalObserver constitutiveExcessWorld = true
coarseSignalObserver geometryArtifactWorld = true
coarseSignalObserver backgroundArtifactWorld = true
coarseSignalObserver nullWorld = false

sourceConstitutiveCollision : Disc.CurrentObserverCollision coarseSignalObserver
sourceConstitutiveCollision =
  Disc.currentObserverCollision sourceOnlyWorld constitutiveExcessWorld refl

------------------------------------------------------------------------
-- Repository-native experimental coordinates.
------------------------------------------------------------------------

data SCGravityCoordinate : Set where
  phaseState
  sourceMassCurrent
  sourceStressEnergy
  sourceGeometry
  probePosition
  externalGravityChannel
  ordinaryBackgroundChannel
  sourceNormalisedResidual
  : SCGravityCoordinate

roleOf : SCGravityCoordinate → Coordinate.CoordinateRole
roleOf phaseState = Coordinate.controlledInput
roleOf sourceMassCurrent = Coordinate.measuredObservable
roleOf sourceStressEnergy = Coordinate.measuredObservable
roleOf sourceGeometry = Coordinate.referenceInvariant
roleOf probePosition = Coordinate.controlledInput
roleOf externalGravityChannel = Coordinate.measuredObservable
roleOf ordinaryBackgroundChannel = Coordinate.nuisanceCoordinate
roleOf sourceNormalisedResidual = Coordinate.derivedDiscriminator

record SCGravityCoordinateReceipt : Set where
  constructor sc-gravity-coordinate-receipt
  field
    coordinate : SCGravityCoordinate
    role : Coordinate.CoordinateRole
    roleIsDeclared : role ≡ roleOf coordinate
    calibrationOrDerivationReference : String

phaseReceipt : SCGravityCoordinateReceipt
phaseReceipt = sc-gravity-coordinate-receipt
  phaseState Coordinate.controlledInput refl
  "temperature/phase calibration with explicit Tc crossing"

sourceCurrentReceipt : SCGravityCoordinateReceipt
sourceCurrentReceipt = sc-gravity-coordinate-receipt
  sourceMassCurrent Coordinate.measuredObservable refl
  "reconstruct J_m from measured current, rotation, mass distribution and phase state"

residualReceipt : SCGravityCoordinateReceipt
residualReceipt = sc-gravity-coordinate-receipt
  sourceNormalisedResidual Coordinate.derivedDiscriminator refl
  "R_C = measured external channel - GR[measured source] - ordinary backgrounds"

------------------------------------------------------------------------
-- Minimal useful joint observation language.
--
-- A field measurement alone leaves sourceOnlyWorld and constitutiveExcessWorld
-- observationally collided.  The joint bundle records source-normalised outcome
-- classes and therefore separates those two worlds by construction.
------------------------------------------------------------------------

data JointObservation : Set where
  sourceExplainsSignal
  constitutiveResidualPersists
  geometryExplainsSignal
  backgroundExplainsSignal
  noSignal
  : JointObservation

jointObserve : HypothesisWorld → JointObservation
jointObserve sourceOnlyWorld = sourceExplainsSignal
jointObserve constitutiveExcessWorld = constitutiveResidualPersists
jointObserve geometryArtifactWorld = geometryExplainsSignal
jointObserve backgroundArtifactWorld = backgroundExplainsSignal
jointObserve nullWorld = noSignal

sourceNormalisedBundle : Disc.ExperimentBundle HypothesisWorld
sourceNormalisedBundle = Disc.experimentBundle
  JointObservation
  jointObserve
  (suc (suc zero))
  "joint source-characterisation plus external-probe experiment"
  "phase, source, geometry, external-probe and nuisance calibration receipts"

sourceVsConstitutiveSeparated :
  Disc.BundleSeparates sourceNormalisedBundle sourceOnlyWorld constitutiveExcessWorld
sourceVsConstitutiveSeparated = Disc.bundleSeparates λ ()

-- Reuse the generic bridge from an experiment bundle into actionability-costed
-- information search.  No new cost-search notion is introduced here.
sourceNormalisedInformationMove : Choice.InformationMove
sourceNormalisedInformationMove = Disc.bundleInformationMove sourceNormalisedBundle

------------------------------------------------------------------------
-- Sequential-plan shape.
--
-- This records the intended adaptive ordering without claiming that one fixed
-- assay must close every live hypothesis.  The generic SequentialConsumerPlan
-- owner supplies the actual dependent outcome-indexed planning semantics.
------------------------------------------------------------------------

data ExperimentStage : Set where
  characteriseSource
  crossPhaseBoundary
  measureExternalProbe
  closeNuisanceChannels
  replicateDiscriminator
  estimateConstitutiveResidual
  : ExperimentStage

nextAfter : ExperimentStage → JointObservation → ExperimentStage
nextAfter characteriseSource sourceExplainsSignal = crossPhaseBoundary
nextAfter characteriseSource constitutiveResidualPersists = crossPhaseBoundary
nextAfter characteriseSource geometryExplainsSignal = measureExternalProbe
nextAfter characteriseSource backgroundExplainsSignal = closeNuisanceChannels
nextAfter characteriseSource noSignal = replicateDiscriminator
nextAfter crossPhaseBoundary sourceExplainsSignal = measureExternalProbe
nextAfter crossPhaseBoundary constitutiveResidualPersists = measureExternalProbe
nextAfter crossPhaseBoundary geometryExplainsSignal = measureExternalProbe
nextAfter crossPhaseBoundary backgroundExplainsSignal = closeNuisanceChannels
nextAfter crossPhaseBoundary noSignal = replicateDiscriminator
nextAfter measureExternalProbe sourceExplainsSignal = estimateConstitutiveResidual
nextAfter measureExternalProbe constitutiveResidualPersists = closeNuisanceChannels
nextAfter measureExternalProbe geometryExplainsSignal = characteriseSource
nextAfter measureExternalProbe backgroundExplainsSignal = closeNuisanceChannels
nextAfter measureExternalProbe noSignal = replicateDiscriminator
nextAfter closeNuisanceChannels sourceExplainsSignal = replicateDiscriminator
nextAfter closeNuisanceChannels constitutiveResidualPersists = replicateDiscriminator
nextAfter closeNuisanceChannels geometryExplainsSignal = characteriseSource
nextAfter closeNuisanceChannels backgroundExplainsSignal = characteriseSource
nextAfter closeNuisanceChannels noSignal = replicateDiscriminator
nextAfter replicateDiscriminator sourceExplainsSignal = estimateConstitutiveResidual
nextAfter replicateDiscriminator constitutiveResidualPersists = estimateConstitutiveResidual
nextAfter replicateDiscriminator geometryExplainsSignal = characteriseSource
nextAfter replicateDiscriminator backgroundExplainsSignal = closeNuisanceChannels
nextAfter replicateDiscriminator noSignal = estimateConstitutiveResidual
nextAfter estimateConstitutiveResidual observation = estimateConstitutiveResidual

------------------------------------------------------------------------
-- Existing proof-search and active-BIDI owners are the admission/orchestration
-- authorities.  The superconducting-gravity lane does not weaken them.
------------------------------------------------------------------------

experimentRouteAdmission : Admission.RouteAdmission
experimentRouteAdmission = Admission.canonicalRouteAdmission

experimentRouteIsLive : Admission.LiveProofSearch
experimentRouteIsLive = Admission.elaborateRoute experimentRouteAdmission

experimentBidiCycle : Loop.BidiPath Loop.liveHypotheses Loop.liveHypotheses
experimentBidiCycle = Loop.canonicalOneIterationCycle

sequentialPlannerBoundary : Sequential.SequentialExperimentPlannerBoundary
sequentialPlannerBoundary = Sequential.canonicalSequentialExperimentPlannerBoundary

proofSearchBoundary : Admission.ProofSearchLeastPrivilegeBoundary
proofSearchBoundary = Admission.canonicalProofSearchLeastPrivilegeBoundary

activeLoopBoundary : Loop.ActiveBidiDiscriminatorLoopBoundary
activeLoopBoundary = Loop.canonicalActiveBidiDiscriminatorLoopBoundary

------------------------------------------------------------------------
-- Current imported frontiers.
------------------------------------------------------------------------

currentSourceSplitFrontier : Split.EnhancementLeaf
currentSourceSplitFrontier = Split.currentFirstOpenEnhancementLeaf

currentPublicEvidenceFrontier : Evidence.EvidenceLeaf
currentPublicEvidenceFrontier = Evidence.currentFirstOpenEvidenceLeaf

------------------------------------------------------------------------
-- Promotion boundaries specific to this cross-pollination.
------------------------------------------------------------------------

record ExperimentDesignProofSearchBoundary : Set where
  constructor experiment-design-proof-search-boundary
  field
    phaseCorrelatedFieldAloneSeparatesSourceFromConstitutive : Bool
    phaseCorrelatedFieldAloneSeparatesSourceFromConstitutiveIsFalse :
      phaseCorrelatedFieldAloneSeparatesSourceFromConstitutive ≡ false

    sourceNormalisedJointBundleSeparatesCanonicalCollision : Bool
    sourceNormalisedJointBundleSeparatesCanonicalCollisionIsTrue :
      sourceNormalisedJointBundleSeparatesCanonicalCollision ≡ true

    oneExperimentMustCloseEveryLiveHypothesis : Bool
    oneExperimentMustCloseEveryLiveHypothesisIsFalse :
      oneExperimentMustCloseEveryLiveHypothesis ≡ false

    nextExperimentMayDependOnOutcome : Bool
    nextExperimentMayDependOnOutcomeIsTrue :
      nextExperimentMayDependOnOutcome ≡ true

    etaCMayBeAddedAsHiddenProofSearchHypothesis : Bool
    etaCMayBeAddedAsHiddenProofSearchHypothesisIsFalse :
      etaCMayBeAddedAsHiddenProofSearchHypothesis ≡ false

    localExperimentLemmaAutomaticallyPromotesPhysics : Bool
    localExperimentLemmaAutomaticallyPromotesPhysicsIsFalse :
      localExperimentLemmaAutomaticallyPromotesPhysics ≡ false

    consumerClosureMayOccurBeforeFullWorldIdentity : Bool
    consumerClosureMayOccurBeforeFullWorldIdentityIsTrue :
      consumerClosureMayOccurBeforeFullWorldIdentity ≡ true

canonicalExperimentDesignProofSearchBoundary : ExperimentDesignProofSearchBoundary
canonicalExperimentDesignProofSearchBoundary =
  experiment-design-proof-search-boundary
    false refl
    true refl
    false refl
    true refl
    false refl
    false refl
    true refl
