module DASHI.Environment.LESBidiResidualRefinementCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.LESApproximateFidelityReductionExact as Approximate

------------------------------------------------------------------------
-- LES cross-pollination: an experiment may be valuable by shrinking the live
-- model/state fibre even when it does not close the consumer in one shot.
------------------------------------------------------------------------

record LESPartialResidualExperiment
    {mechanism : Basis.DomainMechanismSocket}
    (bundle : Synthesis.ExperimentBundle (Basis.State mechanism)) : Set₁ where
  constructor lesPartialResidualExperiment
  field
    prior : Bidi.ResidualFibre (Basis.State mechanism)
    expectedResidualReductionReference : String
    calibrationReference : String
    consumerReference : String
    exactClosureRequired : Bool
    validationReference : String

open LESPartialResidualExperiment public

bundleOutcomeRefinesLESResidual :
  ∀ {mechanism}
    {bundle : Synthesis.ExperimentBundle (Basis.State mechanism)} →
  (experiment : LESPartialResidualExperiment bundle) →
  (outcome : Synthesis.Observation bundle) →
  Bidi.FibreRefines
    (Bidi.MeasuredFibre
      (prior experiment)
      (Synthesis.observe bundle)
      outcome)
    (prior experiment)
bundleOutcomeRefinesLESResidual experiment outcome =
  Bidi.measurementAlwaysRefinesPrior
    (prior experiment)
    (Synthesis.observe _)
    outcome

record LESResidualSequentialBridge
    {mechanism : Basis.DomainMechanismSocket}
    {Prediction : Set}
    (consumer : Basis.State mechanism → Prediction) : Set₁ where
  constructor lesResidualSequentialBridge
  field
    currentFibre : Bidi.ResidualFibre (Basis.State mechanism)
    sequentialPlanReference : String
    partialMeasurementsAllowedReference : String
    terminalClosureStillUsesConsumerIdentifiabilityReference : String
    approximateModelFidelityReference : String
    validationReference : String

open LESResidualSequentialBridge public

record LESBidiResidualBoundary : Set where
  constructor lesBidiResidualBoundary
  field
    usefulLESMeasurementMustCloseConsumerImmediately : Bool
    usefulLESMeasurementMustCloseConsumerImmediatelyIsFalse :
      usefulLESMeasurementMustCloseConsumerImmediately ≡ false
    approximateModelCanCarryShrinkingResidualFibre : Bool
    approximateModelCanCarryShrinkingResidualFibreIsTrue :
      approximateModelCanCarryShrinkingResidualFibre ≡ true
    residualNarrowingMakesApproximateModelExact : Bool
    residualNarrowingMakesApproximateModelExactIsFalse :
      residualNarrowingMakesApproximateModelExact ≡ false
    sequentialPlannerCanUsePartialInformationBeforeClosure : Bool
    sequentialPlannerCanUsePartialInformationBeforeClosureIsTrue :
      sequentialPlannerCanUsePartialInformationBeforeClosure ≡ true

canonicalLESBidiResidualBoundary : LESBidiResidualBoundary
canonicalLESBidiResidualBoundary =
  lesBidiResidualBoundary false refl true refl false refl true refl
