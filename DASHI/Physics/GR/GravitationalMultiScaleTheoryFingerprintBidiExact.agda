module DASHI.Physics.GR.GravitationalMultiScaleTheoryFingerprintBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred

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
    channelMatchesScale : Pred.channel prediction ≡ requiredChannelForScale scale
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
    sameScale : scale scalePrediction ≡ observationScale scaleObservation
    weld : Pred.PredictionObservationWeld
      (prediction scalePrediction) (observation scaleObservation)
open ScaleComparison public

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

    freeFallScaleMatches : scale laboratoryFreeFallPrediction ≡ laboratoryFreeFallScale
    clockScaleMatches : scale laboratoryClockPrediction ≡ laboratoryClockScale
    orbitalScaleMatches : scale orbitalTimingPrediction ≡ orbitalTimingScale
    compactBinaryScaleMatches : scale compactBinaryPrediction ≡ compactBinaryScale
    nanohertzScaleMatches : scale nanohertzTimingPrediction ≡ nanohertzTimingScale
    cosmologicalScaleMatches : scale cosmologicalPropagationPrediction ≡ cosmologicalPropagationScale

    freeFallTheoryIdentityMatches : Pred.theoryCarrier (prediction laboratoryFreeFallPrediction) ≡ theoryIdentity
    clockTheoryIdentityMatches : Pred.theoryCarrier (prediction laboratoryClockPrediction) ≡ theoryIdentity
    orbitalTheoryIdentityMatches : Pred.theoryCarrier (prediction orbitalTimingPrediction) ≡ theoryIdentity
    compactBinaryTheoryIdentityMatches : Pred.theoryCarrier (prediction compactBinaryPrediction) ≡ theoryIdentity
    nanohertzTheoryIdentityMatches : Pred.theoryCarrier (prediction nanohertzTimingPrediction) ≡ theoryIdentity
    cosmologicalTheoryIdentityMatches : Pred.theoryCarrier (prediction cosmologicalPropagationPrediction) ≡ theoryIdentity

    freeFallTheoryFamilyMatches : Pred.theoryFamily (prediction laboratoryFreeFallPrediction) ≡ theoryFamily
    clockTheoryFamilyMatches : Pred.theoryFamily (prediction laboratoryClockPrediction) ≡ theoryFamily
    orbitalTheoryFamilyMatches : Pred.theoryFamily (prediction orbitalTimingPrediction) ≡ theoryFamily
    compactBinaryTheoryFamilyMatches : Pred.theoryFamily (prediction compactBinaryPrediction) ≡ theoryFamily
    nanohertzTheoryFamilyMatches : Pred.theoryFamily (prediction nanohertzTimingPrediction) ≡ theoryFamily
    cosmologicalTheoryFamilyMatches : Pred.theoryFamily (prediction cosmologicalPropagationPrediction) ≡ theoryFamily
open MultiScaleTheoryFingerprint public

------------------------------------------------------------------------
-- Evaluated fingerprint: six comparisons must be comparisons of the exact six
-- prediction slots above.  Merely collecting six comparison receipts is weaker.
------------------------------------------------------------------------

record MultiScaleTheoryEvaluation : Set where
  constructor multi-scale-theory-evaluation
  field
    fingerprint : MultiScaleTheoryFingerprint
    laboratoryFreeFallComparison : ScaleComparison
    laboratoryClockComparison : ScaleComparison
    orbitalTimingComparison : ScaleComparison
    compactBinaryComparison : ScaleComparison
    nanohertzTimingComparison : ScaleComparison
    cosmologicalPropagationComparison : ScaleComparison

    freeFallComparisonMatchesFingerprint :
      scalePrediction laboratoryFreeFallComparison ≡ laboratoryFreeFallPrediction fingerprint
    clockComparisonMatchesFingerprint :
      scalePrediction laboratoryClockComparison ≡ laboratoryClockPrediction fingerprint
    orbitalComparisonMatchesFingerprint :
      scalePrediction orbitalTimingComparison ≡ orbitalTimingPrediction fingerprint
    compactBinaryComparisonMatchesFingerprint :
      scalePrediction compactBinaryComparison ≡ compactBinaryPrediction fingerprint
    nanohertzComparisonMatchesFingerprint :
      scalePrediction nanohertzTimingComparison ≡ nanohertzTimingPrediction fingerprint
    cosmologicalComparisonMatchesFingerprint :
      scalePrediction cosmologicalPropagationComparison ≡ cosmologicalPropagationPrediction fingerprint
open MultiScaleTheoryEvaluation public

data MultiScaleResidual : Set where
  missingObservationScaleContext : MultiScaleResidual
  missingExactScaleSlotReceipt : MultiScaleResidual
  missingSameTheoryIdentityReceipt : MultiScaleResidual
  missingSameTheoryFamilyReceipt : MultiScaleResidual
  missingEvaluationFingerprintWeld : MultiScaleResidual
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
    sixComparisonReceiptsAutomaticallyFormOneFingerprintEvaluation : Bool
    evaluationMustWeldEveryComparisonToFingerprint : Bool
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
    false true false true false true false false false true true false true false

compactBinaryAndCosmologicalChannelsCollide :
  requiredChannelForScale compactBinaryScale ≡ requiredChannelForScale cosmologicalPropagationScale
compactBinaryAndCosmologicalChannelsCollide = refl

compactBinaryAndCosmologicalScalesDistinct :
  compactBinaryScale ≡ cosmologicalPropagationScale → ⊥
compactBinaryAndCosmologicalScalesDistinct ()

laboratoryAndCompactBinaryChannelsDistinct :
  requiredChannelForScale laboratoryFreeFallScale ≡ requiredChannelForScale compactBinaryScale → ⊥
laboratoryAndCompactBinaryChannelsDistinct ()

compactBinaryAndNanohertzChannelsDistinct :
  requiredChannelForScale compactBinaryScale ≡ requiredChannelForScale nanohertzTimingScale → ⊥
compactBinaryAndNanohertzChannelsDistinct ()

clockAndFreeFallChannelsDistinct :
  requiredChannelForScale laboratoryClockScale ≡ requiredChannelForScale laboratoryFreeFallScale → ⊥
clockAndFreeFallChannelsDistinct ()
