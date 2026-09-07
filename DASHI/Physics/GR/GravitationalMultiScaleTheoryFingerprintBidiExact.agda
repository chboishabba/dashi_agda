module DASHI.Physics.GR.GravitationalMultiScaleTheoryFingerprintBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred

------------------------------------------------------------------------
-- MULTI-SCALE GRAVITY THEORY FINGERPRINT
--
-- A candidate gravity theory is not characterized by one successful channel.
-- It exposes predictions across independent observational scales.  Every scale
-- prediction must belong to the same exact theory carrier and family.
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

record ScaleComparison : Set where
  constructor scale-comparison
  field
    scalePrediction : ScalePrediction
    observation : Obs.GravitationalObservationReceipt
    observationChannelMatchesScale :
      Obs.channel observation ≡ requiredChannelForScale (scale scalePrediction)
    weld : Pred.PredictionObservationWeld (prediction scalePrediction) observation

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
  multi-scale-theory-boundary false false false true true false true false

------------------------------------------------------------------------
-- Exact scale non-collapse witnesses.
------------------------------------------------------------------------

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
