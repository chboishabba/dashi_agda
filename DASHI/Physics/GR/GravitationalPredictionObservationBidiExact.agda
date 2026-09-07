module DASHI.Physics.GR.GravitationalPredictionObservationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.GravitationalObservationBidiExact as Obs

------------------------------------------------------------------------
-- PREDICTION <-> OBSERVATION BIDI
--
-- A gravity theory does not compare directly to a detector label.  It must
-- predict the exact observable carried by the calibrated observation channel.
-- The comparison is therefore same-channel and same-observable by construction.
------------------------------------------------------------------------

data GravityTheoryFamily : Set where
  generalRelativityTheory : GravityTheoryFamily
  modifiedGravityTheory : GravityTheoryFamily
  phenomenologicalGravityTheory : GravityTheoryFamily

data PredictionStatus : Set where
  predictionSpecified : PredictionStatus
  predictionResidualOpen : PredictionStatus
  comparisonResidualOpen : PredictionStatus
  comparisonConsistentWithinBudget : PredictionStatus
  comparisonTensionDetected : PredictionStatus

record GravitationalPredictionReceipt : Set where
  constructor gravitational-prediction-receipt
  field
    theoryFamily : GravityTheoryFamily
    theoryCarrier : String
    channel : Obs.GravitationalObservationChannel
    observable : Obs.GravitationalObservable
    observableMatchesChannel : Obs.observableFor channel ≡ observable
    sourceModelCarrier : String
    propagationModelCarrier : String
    detectorResponseCarrier : String
    predictionRevision : String
    exactPredictionLocator : String

open GravitationalPredictionReceipt public

record PredictionObservationWeld
    (prediction : GravitationalPredictionReceipt)
    (observation : Obs.GravitationalObservationReceipt) : Set where
  constructor prediction-observation-weld
  field
    sameChannel : channel prediction ≡ Obs.channel observation
    sameObservable : observable prediction ≡ Obs.observable observation
    sameDataEpochOrTransportReceipt : String
    comparisonMetricCarrier : String
    systematicErrorBudgetCarrier : String
    residualCarrier : String
    residualWithinBudget : Bool

open PredictionObservationWeld public

------------------------------------------------------------------------
-- Reverse residuals.
------------------------------------------------------------------------

data PredictionObservationResidual : Set where
  missingTheoryCarrier : PredictionObservationResidual
  missingSourceModel : PredictionObservationResidual
  missingPropagationModel : PredictionObservationResidual
  missingDetectorResponse : PredictionObservationResidual
  missingPredictionRevision : PredictionObservationResidual
  missingSameChannelReceipt : PredictionObservationResidual
  missingSameObservableReceipt : PredictionObservationResidual
  missingSystematicBudget : PredictionObservationResidual
  missingComparisonMetric : PredictionObservationResidual
  residualRequiresTheoryRevision : PredictionObservationResidual

record PredictionObservationBoundary : Set where
  constructor prediction-observation-boundary
  field
    detectorLabelEqualsTheoryPrediction : Bool
    sameChannelRequired : Bool
    sameObservableRequired : Bool
    detectorResponseRequired : Bool
    systematicBudgetRequired : Bool
    residualAutomaticallyFalsifiesGR : Bool
    betterAlternativeFitAutomaticallyEstablishesAlternative : Bool
    comparisonMayOpenTheoryResidual : Bool

canonicalPredictionObservationBoundary : PredictionObservationBoundary
canonicalPredictionObservationBoundary =
  prediction-observation-boundary
    false true true true true false false true

------------------------------------------------------------------------
-- Finite non-collapse witness.
------------------------------------------------------------------------

data FixturePrediction : Set where
  strainPrediction timingPrediction : FixturePrediction

fixtureChannel : FixturePrediction → Obs.GravitationalObservationChannel
fixtureChannel strainPrediction = Obs.laserInterferometricStrain
fixtureChannel timingPrediction = Obs.pulsarTimingResidual

fixtureObservable : FixturePrediction → Obs.GravitationalObservable
fixtureObservable strainPrediction = Obs.dimensionlessStrain
fixtureObservable timingPrediction = Obs.correlatedArrivalTimeResidual

predictionChannelsDistinct :
  fixtureChannel strainPrediction ≡ fixtureChannel timingPrediction → ⊥
predictionChannelsDistinct ()

predictionObservablesDistinct :
  fixtureObservable strainPrediction ≡ fixtureObservable timingPrediction → ⊥
predictionObservablesDistinct ()
