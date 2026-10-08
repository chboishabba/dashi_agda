module DASHI.Physics.ExoticGravity.AntigravityControlledGWExchangeCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.ControlledEMGravitationalWaveEnergyExchangeExact as Exchange
import DASHI.Physics.GR.ControlledEMGWEinsteinCouplingDegeneracyExact as SignedExchange
import DASHI.Physics.ExoticGravity.AntigravityUnificationInteractionExact as Anti

------------------------------------------------------------------------
-- ANTIGRAVITY x CONTROLLED EM <-> GW ENERGY EXCHANGE
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
-- Same-object comparison weld.  Interaction identity is literal equality.
------------------------------------------------------------------------

record SameObjectExchangeComparison
    (ordinary : AttributedExchangePrediction)
    (alternative : AttributedExchangePrediction)
    (observed : ControlledExchangeObservation) : Set₁ where
  constructor same-object-exchange-comparison
  field
    sameInteractionOrdinaryObservation :
      AttributedExchangePrediction.interaction ordinary
      ≡ ControlledExchangeObservation.interaction observed

    sameInteractionAlternativeObservation :
      AttributedExchangePrediction.interaction alternative
      ≡ ControlledExchangeObservation.interaction observed

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

existingAntigravityBoundary : Anti.AntigravityUnificationBoundary
existingAntigravityBoundary = Anti.canonicalAntigravityUnificationBoundary

------------------------------------------------------------------------
-- Max-cut route: every prediction/observation consumes the literal selected
-- interaction carrier.
------------------------------------------------------------------------

record ControlledExchangeMaxCut : Set₁ where
  constructor controlled-exchange-max-cut
  field
    interaction : Exchange.EMGWInteractionCarrier
    observed : ControlledExchangeObservation
    ordinary : AttributedExchangePrediction
    alternative : AttributedExchangePrediction

    ordinaryUsesInteraction :
      AttributedExchangePrediction.interaction ordinary ≡ interaction
    alternativeUsesInteraction :
      AttributedExchangePrediction.interaction alternative ≡ interaction
    observationUsesInteraction :
      ControlledExchangeObservation.interaction observed ≡ interaction

    conservationPaid : Exchange.StressEnergyConservationReceipt interaction
    workToFrequencyPaid : Exchange.WorkToFrequencyReceipt interaction
    frequencyToPhasePaid : Exchange.FrequencyToPhaseReceipt interaction

    comparison : SameObjectExchangeComparison ordinary alternative observed

    ordinaryComparatorCorrect :
      comparator ordinary ≡ ordinaryGRExchangeComparator
    alternativeComparatorCorrect :
      comparator alternative ≡ alternativeCouplingExchangeComparator

open ControlledExchangeMaxCut public
