module DASHI.Physics.GR.GravitationalMultiScaleTheoryFingerprintBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred

------------------------------------------------------------------------
-- MULTI-SCALE GRAVITY THEORY FINGERPRINT
--
-- Detector channel is not the scale coordinate: compact-binary and
-- cosmological-propagation tests can both consume laser-interferometric strain.
-- A scale-context receipt therefore refines the observation before comparison.
------------------------------------------------------------------------

data GravityScale : Set where
  laboratoryFreeFallScale : GravityScale
  laboratoryClockScale : GravityScale
  orbitalTimingScale : GravityScale
  compactBinaryScale : GravityScale
  nanohertzTimingScale : GravityScale
  cosmologicalPropagationScale : GravityScale

requiredChannelForScale : GravityScale → Obs.GravitationalObservationChannel
requiredChannelForScale laboratoryFreeFallScale = Obs.freeFallEquivalence
requiredChannelForScale laboratoryClockScale = Obs.clockOrRedshift
requiredChannelForScale orbitalTimingScale = Obs.orbitalDecayTiming
requiredChannelForScale compactBinaryScale = Obs.laserInterferometricStrain
requiredChannelForScale nanohertzTimingScale = Obs.pulsarTimingResidual
requiredChannelForScale cosmologicalPropagationScale = Obs.laserInterferometricStrain

record ScalePrediction : Set where
  constructor scale-prediction
  field
    scale : GravityScale
    prediction : Pred.GravitationalPredictionReceipt
    channelMatchesScale :
      Pred.channel prediction ≡ requiredChannelForScale scale

open ScalePrediction public

record ScaleIndexedObservation : Set where
  constructor scale-indexed-observation
  field
    observationScale : GravityScale
    observation : Obs.GravitationalObservationReceipt
    observationChannelMatchesScale :
      Obs.channel observation ≡ requiredChannelForScale observationScale
    scaleContextCarrier : String

open ScaleIndexedObservation public

record ScaleComparison : Set where
  constructor scale-comparison
  field
    scalePrediction : ScalePrediction
    scaleObservation : ScaleIndexedObservation
    sameScale :
      scale scalePrediction ≡ observationScale scaleObservation
    weld :
      Pred.PredictionObservationWeld
        (prediction scalePrediction)
        (observation scaleObservation)

open ScaleComparison public

------------------------------------------------------------------------
-- Theory fingerprint carrier.
------------------------------------------------------------------------

record MultiScaleTheoryFingerprint : Set where
  constructor multi-scale-theory-fingerprint
  field
    theoryIdentity : String
    theoryFamily : Pred.GravityTheoryFamily
    laboratoryFreeFallPrediction : ScalePrediction
    laboratoryClockPrediction : ScalePrediction
    orbitalTimingPrediction : ScalePrediction
    compactBinaryPrediction : ScalePrediction
    nanohertzTimingPrediction : ScalePrediction
    cosmologicalPropagationPrediction : ScalePrediction

    freeFallScaleMatches :
      scale laboratoryFreeFallPrediction ≡ laboratoryFreeFallScale
    clockScaleMatches :
      scale laboratoryClockPrediction ≡ laboratoryClockScale
    orbitalScaleMatches :
      scale orbitalTimingPrediction ≡ orbitalTimingScale
    compactBinaryScaleMatches :
      scale compactBinaryPrediction ≡ compactBinaryScale
    nanohertzScaleMatches :
      scale nanohertzTimingPrediction ≡ nanohertzTimingScale
    cosmologicalScaleMatches :
      scale cosmologicalPropagationPrediction ≡ cosmologicalPropagationScale

    freeFallTheoryIdentityMatches :
      Pred.theoryCarrier (prediction laboratoryFreeFallPrediction) ≡ theoryIdentity
    clockTheoryIdentityMatches :
      Pred.theoryCarrier (prediction laboratoryClockPrediction) ≡ theoryIdentity
    orbitalTheoryIdentityMatches :
      Pred.theoryCarrier (prediction orbitalTimingPrediction) ≡ theoryIdentity
    compactBinaryTheoryIdentityMatches :
      Pred.theoryCarrier (prediction compactBinaryPrediction) ≡ theoryIdentity
    nanohertzTheoryIdentityMatches :
      Pred.theoryCarrier (prediction nanohertzTimingPrediction) ≡ theoryIdentity
    cosmologicalTheoryIdentityMatches :
      Pred.theoryCarrier (prediction cosmologicalPropagationPrediction) ≡ theoryIdentity

    freeFallTheoryFamilyMatches :
      Pred.theoryFamily (prediction laboratoryFreeFallPrediction) ≡ theoryFamily
    clockTheoryFamilyMatches :
      Pred.theoryFamily (prediction laboratoryClockPrediction) ≡ theoryFamily
    orbitalTheoryFamilyMatches :
      Pred.theoryFamily (prediction orbitalTimingPrediction) ≡ theoryFamily
    compactBinaryTheoryFamilyMatches :
      Pred.theoryFamily (prediction compactBinaryPrediction) ≡ theoryFamily
    nanohertzTheoryFamilyMatches :
      Pred.theoryFamily (prediction nanohertzTimingPrediction) ≡ theoryFamily
    cosmologicalTheoryFamilyMatches :
      Pred.theoryFamily (prediction cosmologicalPropagationPrediction) ≡ theoryFamily

open MultiScaleTheoryFingerprint public

------------------------------------------------------------------------
-- Cross-scale residuals and promotion boundary.
------------------------------------------------------------------------

data MultiScaleResidual : Set where
  missingObservationScaleContext : MultiScaleResidual
  missingExactScaleSlotReceipt : MultiScaleResidual
  missingSameTheoryIdentityReceipt : MultiScaleResidual
  missingSameTheoryFamilyReceipt : MultiScaleResidual
  missingLaboratoryFreeFallComparison : MultiScaleResidual
  missingLaboratoryClockComparison : MultiScaleResidual
  missingOrbitalTimingComparison : MultiScaleResidual
  missingCompactBinaryComparison : MultiScaleResidual
  missingNanohertzTimingComparison : MultiScaleResidual
  missingCosmologicalPropagationComparison : MultiScaleResidual
  inconsistentCrossScalePrediction : MultiScaleResidual
  unresolvedCrossScaleSystematics : MultiScaleResidual

record MultiScaleTheoryBoundary : Set where
  constructor multi-scale-theory-boundary
  field
    detectorChannelAloneDeterminesScale : Bool
    observationScaleContextRequired : Bool
    namedSlotAutomaticallyFixesScale : Bool
    exactScaleIdentityRequiredForEverySlot : Bool
    oneScaleAgreementEstablishesAllScaleAgreement : Bool
    laboratoryAnomalyAutomaticallyInvalidatesGWAgreement : Bool
    gwAgreementAutomaticallyClosesLaboratoryResidual : Bool
    sameTheoryIdentityRequiredAcrossScaleComparisons : Bool
    sameTheoryFamilyRequiredAcrossScaleComparisons : Bool
    mixedTheoryPredictionsCountAsOneFingerprint : Bool
    crossScaleTensionMayOpenTheoryRevision : Bool
    completeFingerprintAutomaticallyPromotesUnification : Bool

canonicalMultiScaleTheoryBoundary : MultiScaleTheoryBoundary
canonicalMultiScaleTheoryBoundary =
  multi-scale-theory-boundary
    false true false true false false false true true false true false

------------------------------------------------------------------------
-- Exact introspective collision: same detector channel, different scale.
------------------------------------------------------------------------

compactBinaryAndCosmologicalChannelsCollide :
  requiredChannelForScale compactBinaryScale
    ≡ requiredChannelForScale cosmologicalPropagationScale
compactBinaryAndCosmologicalChannelsCollide = refl

compactBinaryAndCosmologicalScalesDistinct :
  compactBinaryScale ≡ cosmologicalPropagationScale → ⊥
compactBinaryAndCosmologicalScalesDistinct ()

laboratoryAndCompactBinaryChannelsDistinct :
  requiredChannelForScale laboratoryFreeFallScale
    ≡ requiredChannelForScale compactBinaryScale → ⊥
laboratoryAndCompactBinaryChannelsDistinct ()

compactBinaryAndNanohertzChannelsDistinct :
  requiredChannelForScale compactBinaryScale
    ≡ requiredChannelForScale nanohertzTimingScale → ⊥
compactBinaryAndNanohertzChannelsDistinct ()

clockAndFreeFallChannelsDistinct :
  requiredChannelForScale laboratoryClockScale
    ≡ requiredChannelForScale laboratoryFreeFallScale → ⊥
clockAndFreeFallChannelsDistinct ()
