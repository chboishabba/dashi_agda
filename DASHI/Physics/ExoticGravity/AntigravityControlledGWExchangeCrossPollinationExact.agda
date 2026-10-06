module DASHI.Physics.ExoticGravity.AntigravityControlledGWExchangeCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange
import DASHI.Physics.GR.ControlledEMGWEinsteinCouplingDegeneracyExact as SignedExchange
import DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact as Anti

------------------------------------------------------------------------
-- ANTIGRAVITY x CONTROLLED EM <-> GW ENERGY EXCHANGE
--
-- This module installs the Schuetzhold optical-Weber-bar proposal as a new
-- comparison channel in the antigravity programme.  It does not infer
-- antigravity from stimulated GW emission/absorption.  Alternative predictions
-- must be physically distinct on the same interaction: either a re-solved
-- source/metric model or an explicit modified local photon-graviton coupling.
-- Merely relabelling the Einstein source coupling sign while freezing the same
-- physical h_{mu nu} and T_{mu nu} is intentionally rejected.
------------------------------------------------------------------------

data GravityExchangeComparator : Set where
  ordinaryGRExchangeComparator : GravityExchangeComparator
  alternativeCouplingExchangeComparator : GravityExchangeComparator

data ExchangeObservationChannel : Set where
  opticalFrequencyShift : ExchangeObservationChannel
  delayedOpticalPhaseShift : ExchangeObservationChannel
  interferenceVisibility : ExchangeObservationChannel
  beatingSignature : ExchangeObservationChannel

data ExchangeClaimStatus : Set where
  calibratedExchangeObservation : ExchangeClaimStatus
  ordinaryGRResidualOpen : ExchangeClaimStatus
  alternativeResidualOpen : ExchangeClaimStatus
  discriminatingResidualEstablished : ExchangeClaimStatus

record AttributedExchangePrediction : Set₁ where
  constructor attributed-exchange-prediction
  field
    comparator : GravityExchangeComparator
    interaction : Exchange.EMGWInteractionCarrier
    Prediction : Set
    prediction : Prediction
    AttributionReceipt : Set
    attributionReceipt : AttributionReceipt

open AttributedExchangePrediction public

record ControlledExchangeObservation : Set₁ where
  constructor controlled-exchange-observation
  field
    interaction : Exchange.EMGWInteractionCarrier
    channel : ExchangeObservationChannel
    Observation : Set
    observation : Observation
    CalibrationReceipt : Set
    calibrationReceipt : CalibrationReceipt
    ReversalReceipt : Set
    reversalReceipt : ReversalReceipt

open ControlledExchangeObservation public

------------------------------------------------------------------------
-- Same-object comparison weld.
------------------------------------------------------------------------

record SameObjectExchangeComparison
    (ordinary : AttributedExchangePrediction)
    (alternative : AttributedExchangePrediction)
    (observed : ControlledExchangeObservation) : Set₁ where
  constructor same-object-exchange-comparison
  field
    SameInteractionOrdinaryObservation : Set
    sameInteractionOrdinaryObservation : SameInteractionOrdinaryObservation

    SameInteractionAlternativeObservation : Set
    sameInteractionAlternativeObservation : SameInteractionAlternativeObservation

    AlternativeIsPhysicallyDistinctReceipt : Set
    alternativeIsPhysicallyDistinctReceipt : AlternativeIsPhysicallyDistinctReceipt

    OrdinaryResidual : Set
    ordinaryResidual : OrdinaryResidual

    AlternativeResidual : Set
    alternativeResidual : AlternativeResidual

    ResidualOrderingReceipt : Set
    residualOrderingReceipt : ResidualOrderingReceipt

    status : ExchangeClaimStatus

open SameObjectExchangeComparison public

------------------------------------------------------------------------
-- Promotion and model-identity firewall.
------------------------------------------------------------------------

record AntigravityExchangeBoundary : Set where
  constructor antigravity-exchange-boundary
  field
    controlledGWExchangeIsNewObservationChannel : Bool
    controlledGWExchangeAloneProvesAntigravity : Bool
    controlledGWExchangeAloneProvesModifiedGravity : Bool
    stimulatedEmissionLanguageAloneProvesGravitons : Bool
    ordinaryGRPredictionMustBeInstantiated : Bool
    alternativePredictionMustUseSamePhysicalInteraction : Bool
    calibratedObservationMustUseSamePhysicalInteraction : Bool
    reversalControlRequiredForSignSensitiveClaim : Bool
    residualComparisonMayDiscriminateModels : Bool
    modelDiscriminationMayRefineAntigravityExperimentDesign : Bool
    fixedHNaiveEinsteinSignRelabelCountsAsAlternativeModel : Bool
    signedGAlternativeMustResolveSourceOrModifyLocalCoupling : Bool

canonicalAntigravityExchangeBoundary : AntigravityExchangeBoundary
canonicalAntigravityExchangeBoundary =
  antigravity-exchange-boundary
    true false false false true true true true true true false true

existingSignedExchangeBoundary : SignedExchange.ControlledExchangeSignedGBoundary
existingSignedExchangeBoundary =
  SignedExchange.canonicalControlledExchangeSignedGBoundary

------------------------------------------------------------------------
-- Existing antigravity architecture remains authoritative.
------------------------------------------------------------------------

existingAntigravityBoundary : Anti.AntigravityUnificationBoundary
existingAntigravityBoundary = Anti.canonicalAntigravityUnificationBoundary

------------------------------------------------------------------------
-- Max-cut route encoded as obligations rather than prose promotion.
------------------------------------------------------------------------

record ControlledExchangeMaxCut : Set₁ where
  constructor controlled-exchange-max-cut
  field
    interaction : Exchange.EMGWInteractionCarrier
    observed : ControlledExchangeObservation
    ordinary : AttributedExchangePrediction
    alternative : AttributedExchangePrediction

    conservationPaid : Exchange.StressEnergyConservationReceipt interaction
    workToFrequencyPaid : Exchange.WorkToFrequencyReceipt interaction
    frequencyToPhasePaid : Exchange.FrequencyToPhaseReceipt interaction

    comparison : SameObjectExchangeComparison ordinary alternative observed

    ordinaryComparatorCorrect :
      comparator ordinary ≡ ordinaryGRExchangeComparator
    alternativeComparatorCorrect :
      comparator alternative ≡ alternativeCouplingExchangeComparator

open ControlledExchangeMaxCut public
