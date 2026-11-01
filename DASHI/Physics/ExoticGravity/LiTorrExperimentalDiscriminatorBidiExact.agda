module DASHI.Physics.ExoticGravity.LiTorrExperimentalDiscriminatorBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalBidiExact as B
import DASHI.Physics.ExoticGravity.LiTorrCoupledPotentialModelExact as LT
import DASHI.Physics.ExoticGravity.LiTorrKowittMagnitudeDisputeBidiExact as K

------------------------------------------------------------------------
-- LI--TORR EXPERIMENTAL DISCRIMINATOR
--
-- A claimed superconducting gravity-channel effect must be distinguishable
-- from ordinary magnetic, mechanical, thermal, vibration, and pickup effects.
-- The discriminator is routed from the claimed field channel backward to the
-- measurements needed to own that claim.
------------------------------------------------------------------------

data PhaseState : Set where
  normalPhase : PhaseState
  superconductingPhase : PhaseState

data DriveState : Set where
  staticDrive : DriveState
  timeDependentDrive : DriveState

data ProbeClass : Set where
  localApparatusProbe : ProbeClass
  electricallyIsolatedTestMass : ProbeClass
  inertialReferenceProbe : ProbeClass
  clockOrPhaseProbe : ProbeClass

record LiTorrTestCell : Set where
  constructor li-torr-test-cell
  field
    phase : PhaseState
    drive : DriveState
    probe : ProbeClass
    magneticFieldMatched : Bool
    geometryMatched : Bool
    temperatureMatchedAsFarAsPossible : Bool
    vibrationMonitored : Bool
    electromagneticPickupMonitored : Bool
    note : String

open LiTorrTestCell public

------------------------------------------------------------------------
-- Phase-crossing discriminator.
--
-- If coherence is the claimed causal coordinate, a same-apparatus comparison
-- across the superconducting transition is more probative than comparing two
-- unrelated devices.
------------------------------------------------------------------------

record PhaseCrossingBidi : Set where
  constructor phase-crossing-bidi
  field
    sameMaterialPreferred : Bool
    sameMaterialPreferredIsTrue : sameMaterialPreferred ≡ true

    sameGeometryPreferred : Bool
    sameGeometryPreferredIsTrue : sameGeometryPreferred ≡ true

    phaseOnOffRequired : Bool
    phaseOnOffRequiredIsTrue : phaseOnOffRequired ≡ true

    matchedEMDriveRequired : Bool
    matchedEMDriveRequiredIsTrue : matchedEMDriveRequired ≡ true

canonicalPhaseCrossingBidi : PhaseCrossingBidi
canonicalPhaseCrossingBidi = phase-crossing-bidi
  true refl true refl true refl true refl

------------------------------------------------------------------------
-- Channel discriminators.
------------------------------------------------------------------------

record ChannelDiscriminatorMatrix : Set where
  constructor channel-discriminator-matrix
  field
    localForceAloneSupportsGravityField : Bool
    localForceAloneSupportsGravityFieldIsFalse :
      localForceAloneSupportsGravityField ≡ false

    remoteIsolatedMassResponseStrengthensFieldClaim : Bool
    remoteIsolatedMassResponseStrengthensFieldClaimIsTrue :
      remoteIsolatedMassResponseStrengthensFieldClaim ≡ true

    freeFallChangeStrengthensPassiveGravityClaim : Bool
    freeFallChangeStrengthensPassiveGravityClaimIsTrue :
      freeFallChangeStrengthensPassiveGravityClaim ≡ true

    timeDependentDriveShouldBeCheckedForInductivePickup : Bool
    timeDependentDriveShouldBeCheckedForInductivePickupIsTrue :
      timeDependentDriveShouldBeCheckedForInductivePickup ≡ true

    metricOrClockSignatureIsDistinctFromThrust : Bool
    metricOrClockSignatureIsDistinctFromThrustIsTrue :
      metricOrClockSignatureIsDistinctFromThrust ≡ true

canonicalChannelDiscriminatorMatrix : ChannelDiscriminatorMatrix
canonicalChannelDiscriminatorMatrix = channel-discriminator-matrix
  false refl true refl true refl true refl true refl

------------------------------------------------------------------------
-- Magnitude-specific BIDI reopening.
--
-- Because the historical magnitude enhancement is contested at the
-- constitutive/permeability step, an experiment cannot merely verify that a
-- superconductor exhibits the Meissner effect.  It must measure a separate
-- gravity-channel residual with scaling tied to the proposed source variable.
------------------------------------------------------------------------

record MagnitudeReopeningCutset : Set where
  constructor magnitude-reopening-cutset
  field
    meissnerObservationAloneReopensGravityMagnitude : Bool
    meissnerObservationAloneReopensGravityMagnitudeIsFalse :
      meissnerObservationAloneReopensGravityMagnitude ≡ false

    gravityChannelObservableRequired : Bool
    gravityChannelObservableRequiredIsTrue :
      gravityChannelObservableRequired ≡ true

    sourceScalingSweepRequired : Bool
    sourceScalingSweepRequiredIsTrue :
      sourceScalingSweepRequired ≡ true

    phaseCorrelationRequired : Bool
    phaseCorrelationRequiredIsTrue : phaseCorrelationRequired ≡ true

    ordinaryBackgroundScalingMustBeModelled : Bool
    ordinaryBackgroundScalingMustBeModelledIsTrue :
      ordinaryBackgroundScalingMustBeModelled ≡ true

canonicalMagnitudeReopeningCutset : MagnitudeReopeningCutset
canonicalMagnitudeReopeningCutset = magnitude-reopening-cutset
  false refl true refl true refl true refl true refl

------------------------------------------------------------------------
-- Forward predictions kept separate by drive class.
------------------------------------------------------------------------

record StaticVsDynamicPredictionBoundary : Set where
  constructor static-vs-dynamic-prediction-boundary
  field
    staticAlignedAngularMomentumTargetsGravitomagneticChannel : Bool
    staticAlignedAngularMomentumTargetsGravitomagneticChannelIsTrue :
      staticAlignedAngularMomentumTargetsGravitomagneticChannel ≡ true

    timeDependentVectorPotentialTargetsGravitoelectricChannel : Bool
    timeDependentVectorPotentialTargetsGravitoelectricChannelIsTrue :
      timeDependentVectorPotentialTargetsGravitoelectricChannel ≡ true

    observingOneChannelEstablishesTheOther : Bool
    observingOneChannelEstablishesTheOtherIsFalse :
      observingOneChannelEstablishesTheOther ≡ false

canonicalStaticVsDynamicPredictionBoundary : StaticVsDynamicPredictionBoundary
canonicalStaticVsDynamicPredictionBoundary =
  static-vs-dynamic-prediction-boundary true refl true refl false refl

------------------------------------------------------------------------
-- Strong fail-closed promotion condition.
------------------------------------------------------------------------

record LiTorrPromotionReceipt : Set where
  constructor li-torr-promotion-receipt
  field
    phaseCorrelatedResidual : Bool
    remoteOrFreeFallGravityProbe : Bool
    magneticAndMechanicalBackgroundClosed : Bool
    scalingCompatibleWithClaimedSource : Bool
    independentReplication : Bool

record LiTorrPromotionBoundary : Set where
  constructor li-torr-promotion-boundary
  field
    anomalousLocalForceEnough : Bool
    anomalousLocalForceEnoughIsFalse : anomalousLocalForceEnough ≡ false

    phaseChangeAloneEnough : Bool
    phaseChangeAloneEnoughIsFalse : phaseChangeAloneEnough ≡ false

    independentChannelSpecificResidualRequired : Bool
    independentChannelSpecificResidualRequiredIsTrue :
      independentChannelSpecificResidualRequired ≡ true

canonicalLiTorrPromotionBoundary : LiTorrPromotionBoundary
canonicalLiTorrPromotionBoundary =
  li-torr-promotion-boundary false refl false refl true refl
