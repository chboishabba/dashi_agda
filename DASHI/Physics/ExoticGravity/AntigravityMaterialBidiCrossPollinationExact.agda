module DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.DialecticalMaterialFutureSafetyExact as Future
import DASHI.Core.DialecticalMaterialRevisionExact as Revision
import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalBidiExact as Gravity

------------------------------------------------------------------------
-- ANTIGRAVITY AS A REVERSE-SEARCH LABEL, NOT AN OBSERVABLE
--
-- The phrase "antigravity" is too coarse to be a physical receipt.  It must be
-- decomposed into a typed claim before any reverse acquisition or promotion.
------------------------------------------------------------------------

data AntigravityClaim : Set where
  reducedPassiveWeight : AntigravityClaim
  changedFreeFallResponse : AntigravityClaim
  remoteRepulsiveField : AntigravityClaim
  alteredInertialResponse : AntigravityClaim
  persistentPropulsiveImpulse : AntigravityClaim
  engineeredMetricResponse : AntigravityClaim

data RequiredDiscriminator : Set where
  staticLoadDiscriminator : RequiredDiscriminator
  freeFallDiscriminator : RequiredDiscriminator
  externalTestMassDiscriminator : RequiredDiscriminator
  inertialComparisonDiscriminator : RequiredDiscriminator
  momentumClosureDiscriminator : RequiredDiscriminator
  metricClockDiscriminator : RequiredDiscriminator

requiredDiscriminator : AntigravityClaim → RequiredDiscriminator
requiredDiscriminator reducedPassiveWeight = staticLoadDiscriminator
requiredDiscriminator changedFreeFallResponse = freeFallDiscriminator
requiredDiscriminator remoteRepulsiveField = externalTestMassDiscriminator
requiredDiscriminator alteredInertialResponse = inertialComparisonDiscriminator
requiredDiscriminator persistentPropulsiveImpulse = momentumClosureDiscriminator
requiredDiscriminator engineeredMetricResponse = metricClockDiscriminator

requiredObservable : AntigravityClaim → Gravity.Observable
requiredObservable reducedPassiveWeight = Gravity.staticWeightChange
requiredObservable changedFreeFallResponse = Gravity.freeFallAccelerationChange
requiredObservable remoteRepulsiveField = Gravity.localTestMassAcceleration
requiredObservable alteredInertialResponse = Gravity.inertialResponseChange
requiredObservable persistentPropulsiveImpulse = Gravity.vacuumPersistentThrust
requiredObservable engineeredMetricResponse = Gravity.metricOrClockShift

------------------------------------------------------------------------
-- MATERIAL-REGIME INDEX
--
-- The same declared apparatus/claim surface can require renewed evaluation when
-- the relevant material regime changes.  This imports #802's future-safety
-- principle without treating material change itself as evidence for antigravity.
------------------------------------------------------------------------

data AntigravityMaterialRegime : Set where
  ordinaryRegime : AntigravityMaterialRegime
  coherentRegime : AntigravityMaterialRegime
  highFieldRegime : AntigravityMaterialRegime
  rotatingRegime : AntigravityMaterialRegime
  vacuumRegime : AntigravityMaterialRegime
  reorganisedRegime : AntigravityMaterialRegime

record AntigravityBidiRequest : Set where
  constructor antigravity-bidi-request
  field
    claim : AntigravityClaim
    materialRegime : AntigravityMaterialRegime
    declaredSurface : String
    requiredDiscriminatorReceipt : RequiredDiscriminator
    discriminatorMatchesClaim : requiredDiscriminator claim ≡ requiredDiscriminatorReceipt

open AntigravityBidiRequest public

record AntigravityPromotionBoundary : Set where
  constructor antigravity-promotion-boundary
  field
    coarseAntigravityLabelIsPhysicalObservable : Bool
    typedDiscriminatorRequired : Bool
    changedMaterialRegimeAutomaticallyValidatesClaim : Bool
    anomalousForceAloneClosesGravityMechanism : Bool
    ordinaryResidualClosureStillRequired : Bool
    changedMaterialRegimeMayReopenEvaluation : Bool
    materialRefinementCreatesActionAuthority : Bool

canonicalAntigravityPromotionBoundary : AntigravityPromotionBoundary
canonicalAntigravityPromotionBoundary =
  antigravity-promotion-boundary
    false true false false true true false

------------------------------------------------------------------------
-- Existing boundaries reused rather than restated as new physics.
------------------------------------------------------------------------

existingGravityCutset : Gravity.GravityMechanismBidiCutset
existingGravityCutset = Gravity.canonicalGravityMechanismBidiCutset

existingMaterialFutureSafetyBoundary : Future.DialecticalMaterialFutureSafetyBoundary
existingMaterialFutureSafetyBoundary = Future.canonicalDialecticalMaterialFutureSafetyBoundary

existingMaterialRevisionBoundary : Revision.DialecticalMaterialRevisionBoundary
existingMaterialRevisionBoundary = Revision.canonicalDialecticalMaterialRevisionBoundary

------------------------------------------------------------------------
-- Exact finite witness: same coarse label, different material regime, different
-- reverse acquisition demand.  The repair is to retain the regime coordinate.
------------------------------------------------------------------------

data FixtureWorld : Set where
  ambientFixture vacuumFixture : FixtureWorld

data CoarseLabel : Set where
  antigravityLikeSignal : CoarseLabel

data AcquisitionDemand : Set where
  ordinaryMomentumAudit vacuumMomentumAudit : AcquisitionDemand

coarseObserve : FixtureWorld → CoarseLabel
coarseObserve _ = antigravityLikeSignal

fixtureRegime : FixtureWorld → AntigravityMaterialRegime
fixtureRegime ambientFixture = ordinaryRegime
fixtureRegime vacuumFixture = vacuumRegime

acquisitionDemand : FixtureWorld → AcquisitionDemand
acquisitionDemand ambientFixture = ordinaryMomentumAudit
acquisitionDemand vacuumFixture = vacuumMomentumAudit

coarseCollision :
  coarseObserve ambientFixture ≡ coarseObserve vacuumFixture
coarseCollision = refl

coarseLabelDoesNotFixAcquisitionDemand :
  acquisitionDemand ambientFixture ≡ acquisitionDemand vacuumFixture → ⊥
coarseLabelDoesNotFixAcquisitionDemand ()

refinedObserve : FixtureWorld → CoarseLabel × AntigravityMaterialRegime
refinedObserve world = coarseObserve world , fixtureRegime world

refinedSeparatesFixture :
  refinedObserve ambientFixture ≡ refinedObserve vacuumFixture → ⊥
refinedSeparatesFixture ()
