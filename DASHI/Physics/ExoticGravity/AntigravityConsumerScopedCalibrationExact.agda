module DASHI.Physics.ExoticGravity.AntigravityConsumerScopedCalibrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityExecutionCalibrationExact as Calibration
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- CONSUMER-SCOPED CALIBRATION
--
-- A calibration/refinement receipt is not generically adequate for every
-- antigravity consumer.  Adequacy is indexed by the exact claim and therefore
-- by the exact discriminator required by that claim.
------------------------------------------------------------------------

record ConsumerScopedCalibration
    (claim : Anti.AntigravityClaim) : Set₁ where
  constructor consumer-scoped-calibration
  field
    calibration : Calibration.ExecutionCalibrationReceipt
    discriminator : Anti.RequiredDiscriminator
    discriminatorMatchesClaim :
      Anti.requiredDiscriminator claim ≡ discriminator

    ConsumerAdequacy : Anti.RequiredDiscriminator → Set
    adequacyForRequiredDiscriminator : ConsumerAdequacy discriminator

open ConsumerScopedCalibration public

requiredCalibrationDiscriminator :
  {claim : Anti.AntigravityClaim} →
  ConsumerScopedCalibration claim → Anti.RequiredDiscriminator
requiredCalibrationDiscriminator scoped = discriminator scoped

------------------------------------------------------------------------
-- Exact finite collision: one generic "calibrated" label cannot determine the
-- consumer-specific discriminator adequacy required downstream.
------------------------------------------------------------------------

data CalibrationFixture : Set where
  staticLoadCalibration freeFallCalibration : CalibrationFixture

data CoarseCalibrationState : Set where
  calibrated : CoarseCalibrationState

coarseCalibrationObserve : CalibrationFixture → CoarseCalibrationState
coarseCalibrationObserve _ = calibrated

fixtureDiscriminator : CalibrationFixture → Anti.RequiredDiscriminator
fixtureDiscriminator staticLoadCalibration = Anti.staticLoadDiscriminator
fixtureDiscriminator freeFallCalibration = Anti.freeFallDiscriminator

coarseCalibrationCollision :
  coarseCalibrationObserve staticLoadCalibration
    ≡ coarseCalibrationObserve freeFallCalibration
coarseCalibrationCollision = refl

coarseCalibrationDoesNotDetermineDiscriminator :
  fixtureDiscriminator staticLoadCalibration
    ≡ fixtureDiscriminator freeFallCalibration → ⊥
coarseCalibrationDoesNotDetermineDiscriminator ()

------------------------------------------------------------------------
-- Reverse residuals.
------------------------------------------------------------------------

data ConsumerCalibrationResidual : Set where
  missingConsumerClaim : ConsumerCalibrationResidual
  missingRequiredDiscriminatorBinding : ConsumerCalibrationResidual
  missingConsumerAdequacyFamily : ConsumerCalibrationResidual
  missingConsumerAdequacyWitness : ConsumerCalibrationResidual

producerForConsumerCalibrationResidual :
  ConsumerCalibrationResidual → Search.ProducerClass
producerForConsumerCalibrationResidual missingConsumerClaim = Search.discriminatorProducer
producerForConsumerCalibrationResidual missingRequiredDiscriminatorBinding = Search.identityProducer
producerForConsumerCalibrationResidual missingConsumerAdequacyFamily = Search.discriminatorProducer
producerForConsumerCalibrationResidual missingConsumerAdequacyWitness = Search.empiricalEvidenceProducer

record ConsumerScopedCalibrationBoundary : Set where
  constructor consumer-scoped-calibration-boundary
  field
    genericCalibrationAdequacyEqualsConsumerAdequacy : Bool
    exactClaimDiscriminatorBindingRequired : Bool
    staticLoadCalibrationAutomaticallyPaysFreeFallCalibration : Bool
    freeFallCalibrationAutomaticallyPaysMetricClockCalibration : Bool
    consumerScopedCalibrationAutomaticallyValidatesMechanism : Bool

canonicalConsumerScopedCalibrationBoundary : ConsumerScopedCalibrationBoundary
canonicalConsumerScopedCalibrationBoundary =
  consumer-scoped-calibration-boundary false true false false false
