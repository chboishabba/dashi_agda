module DASHI.Environment.LESBidiResidualRefinementCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.AdaptiveFidelityConsumerMarginExact as Fidelity
import DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact as ApproxCore
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.LESApproximateFidelityReductionExact as Approximate

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
bundleOutcomeRefinesLESResidual {bundle = bundle} experiment outcome =
  Bidi.measurementAlwaysRefinesPrior
    (prior experiment)
    (Synthesis.observe bundle)
    outcome

record ResidualQualifiedLESApproximateDecision
    {mechanism : Basis.DomainMechanismSocket}
    {Summary Decision : Set}
    (model : Approximate.LESApproximateReduction mechanism Summary)
    (decide : Summary → Decision) : Set₁ where
  constructor residualQualifiedLESApproximateDecision
  field
    decisionCertificate :
      Approximate.LESApproximateDecisionCertificate model decide
    residualFibre : Bidi.ResidualFibre (Basis.State mechanism)
    residualReceipt : Bidi.ApproximateResidualReceipt residualFibre
    residualInterpretationReference : String
    richerConsumerStillOpenReference : String

open ResidualQualifiedLESApproximateDecision public

residualQualifiedApproximateDecisionStillSafe :
  ∀ {mechanism Summary Decision}
    {model : Approximate.LESApproximateReduction mechanism Summary}
    {decide : Summary → Decision} →
  ResidualQualifiedLESApproximateDecision model decide →
  (controls : List (Basis.Control mechanism)) →
  (state : Basis.State mechanism) →
  decide
    (Fidelity.low
      (ApproxCore.approximateTraceFidelityPair
        (Approximate.asApproximateTraceReduction model))
      (controls , state))
  ≡ decide
    (Fidelity.high
      (ApproxCore.approximateTraceFidelityPair
        (Approximate.asApproximateTraceReduction model))
      (controls , state))
residualQualifiedApproximateDecisionStillSafe receipt controls state =
  Approximate.lesApproximateDecisionSafe
    (decisionCertificate receipt)
    controls
    state

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
    decisionSafetyAutomaticallyClosesMechanisticResidual : Bool
    decisionSafetyAutomaticallyClosesMechanisticResidualIsFalse :
      decisionSafetyAutomaticallyClosesMechanisticResidual ≡ false

canonicalLESBidiResidualBoundary : LESBidiResidualBoundary
canonicalLESBidiResidualBoundary =
  lesBidiResidualBoundary
    false refl true refl false refl true refl false refl
