module DASHI.Culture.AmyEskridgeAntigravityExperimentBindingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (zero; suc)

import DASHI.Core.DiscriminatorSynthesisExact as Disc
import DASHI.Culture.AmyEskridgeAntigravityObservationBidiCrossPollinationExact as AmyBidi
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentDesignProofSearchCrossPollinationExact as SC
import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs

------------------------------------------------------------------------
-- AMY REVERSE PROJECTION -> CONSUMER/CHANNEL-BOUND EXPERIMENT
--
-- The existing superconducting-gravity bundle already separates source-only
-- from constitutive-excess worlds.  Its external-gravity coordinate is generic,
-- however.  This adapter refines only that missing coordinate: the exact
-- observation channel demanded by the live Amy/#828 consumer projection.
------------------------------------------------------------------------

record ChannelBoundJointObservation
    (projection : AmyBidi.AmyGravityReverseSearchProjection) : Set where
  constructor channel-bound-joint-observation
  field
    observationChannel : Obs.GravitationalObservationChannel
    observationChannelMatchesProjection :
      observationChannel ≡ AmyBidi.observationChannel projection
    jointObservation : SC.JointObservation

open ChannelBoundJointObservation public

channelBoundObserve :
  (projection : AmyBidi.AmyGravityReverseSearchProjection) →
  SC.HypothesisWorld →
  ChannelBoundJointObservation projection
channelBoundObserve projection world =
  channel-bound-joint-observation
    (AmyBidi.observationChannel projection)
    refl
    (SC.jointObserve world)

channelBoundBundle :
  (projection : AmyBidi.AmyGravityReverseSearchProjection) →
  Disc.ExperimentBundle SC.HypothesisWorld
channelBoundBundle projection =
  Disc.experimentBundle
    (ChannelBoundJointObservation projection)
    (channelBoundObserve projection)
    (suc (suc zero))
    "Amy/#828 consumer-bound source-characterisation plus external-probe experiment"
    "existing superconducting-gravity joint bundle refined by exact consumer observation channel"

channelBoundStillSeparatesSourceVsConstitutive :
  (projection : AmyBidi.AmyGravityReverseSearchProjection) →
  Disc.BundleSeparates
    (channelBoundBundle projection)
    SC.sourceOnlyWorld
    SC.constitutiveExcessWorld
channelBoundStillSeparatesSourceVsConstitutive projection =
  Disc.bundleSeparates λ ()

------------------------------------------------------------------------
-- Exact live-demand binding.  The experiment entrypoint is no longer merely
-- "about the same mechanism family"; it is indexed by the exact projection,
-- typed discriminator, and observation channel consumed downstream.
------------------------------------------------------------------------

record AmyConsumerBoundExperimentDemand
    (projection : AmyBidi.AmyGravityReverseSearchProjection) : Set where
  constructor amy-consumer-bound-experiment-demand
  field
    request : Anti.AntigravityBidiRequest
    requestMatchesProjection : request ≡ AmyBidi.request projection

    discriminator : Anti.RequiredDiscriminator
    discriminatorMatchesProjection :
      discriminator ≡ Anti.requiredDiscriminator (AmyBidi.derivedClaim projection)

    observationChannel : Obs.GravitationalObservationChannel
    channelMatchesProjection :
      observationChannel ≡ AmyBidi.observationChannel projection

    experimentBundle : Disc.ExperimentBundle SC.HypothesisWorld
    experimentBundleMatchesProjection :
      experimentBundle ≡ channelBoundBundle projection

    calibrationOrDerivationCarrier : String

open AmyConsumerBoundExperimentDemand public

amyLiTorrFreeFallExperimentDemand :
  AmyConsumerBoundExperimentDemand AmyBidi.amyLiTorrFreeFallProjection
amyLiTorrFreeFallExperimentDemand =
  amy-consumer-bound-experiment-demand
    (AmyBidi.request AmyBidi.amyLiTorrFreeFallProjection)
    refl
    Anti.freeFallDiscriminator
    refl
    Obs.freeFallEquivalence
    refl
    (channelBoundBundle AmyBidi.amyLiTorrFreeFallProjection)
    refl
    "free-fall calibration/derivation receipt required by the live consumer"

amyLiTorrRemoteFieldExperimentDemand :
  AmyConsumerBoundExperimentDemand AmyBidi.amyLiTorrRemoteFieldProjection
amyLiTorrRemoteFieldExperimentDemand =
  amy-consumer-bound-experiment-demand
    (AmyBidi.request AmyBidi.amyLiTorrRemoteFieldProjection)
    refl
    Anti.externalTestMassDiscriminator
    refl
    Obs.localTestMassAcceleration
    refl
    (channelBoundBundle AmyBidi.amyLiTorrRemoteFieldProjection)
    refl
    "remote external-test-mass calibration/derivation receipt required by the live consumer"

------------------------------------------------------------------------
-- Introspective non-collapse.  The underlying historical mechanism and source
-- vs constitutive hypothesis pair may be the same, while the live experiments
-- require different observation channels.
------------------------------------------------------------------------

freeFallAndRemoteExperimentChannelsDistinct :
  observationChannel amyLiTorrFreeFallExperimentDemand
    ≡ observationChannel amyLiTorrRemoteFieldExperimentDemand → ⊥
freeFallAndRemoteExperimentChannelsDistinct ()

record AmyExperimentBindingBoundary : Set where
  constructor amy-experiment-binding-boundary
  field
    historicalMechanismIdentityAloneSelectsExperimentChannel : Bool
    genericExternalGravityBundleAutomaticallyPaysConsumerChannel : Bool
    consumerSpecificProjectionRequired : Bool
    exactDiscriminatorRequired : Bool
    exactObservationChannelRequired : Bool
    channelRefinementChangesHistoricalAmyAttribution : Bool
    channelBoundBundleAutomaticallyProvesPhysics : Bool

canonicalAmyExperimentBindingBoundary : AmyExperimentBindingBoundary
canonicalAmyExperimentBindingBoundary =
  amy-experiment-binding-boundary
    false false true true true false false
