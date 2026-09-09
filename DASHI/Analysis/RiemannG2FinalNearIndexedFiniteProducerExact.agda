module DASHI.Analysis.RiemannG2FinalNearIndexedFiniteProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval

------------------------------------------------------------------------
-- FINAL-NEAR-INDEXED CARRIER-NEUTRAL FINITE PRODUCER
--
-- Choose the evaluation scalar to be the actual final nearResponseAt(chosen J)
-- by construction.  This removes a downstream same-object equality from the
-- preferred direct route.  The producer must still carry a real evaluation
-- receipt and budget extraction; nothing analytic is fabricated.
------------------------------------------------------------------------

record FinalNearIndexedFiniteInput
    {S : NearFar.OrderedAdditiveNearFarSurface}
    {transport : Transport.ExplicitCutoffNearFarAgdaTransport S}
    (offInput : Direct.DirectLiteralOffTargetInput S transport) : Set₁ where
  private
    Scalar = NearFar.Scalar S
    finalNear = Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
  field
    route : Eval.FiniteNearRoute
    routeAdmissible : Eval.AdmissibleFiniteNearRoute route
    preservation : Eval.PhasePreservingFiniteNearRoute route

    Error : Set
    approximant : Scalar
    error : Error
    Within : Scalar -> Scalar -> Error -> Set
    withinEvaluation : Within finalNear approximant error
    evaluationReference : String

    Budget : Set
    nearBudget : Budget
    ProducesRequiredUpper :
      Eval.SignedFiniteNearEvaluationSurface -> Budget -> Set

    producesRequiredUpper :
      ProducesRequiredUpper
        (Eval.signed-finite-near-evaluation-surface
          Scalar Error finalNear approximant error Within
          withinEvaluation evaluationReference)
        nearBudget

    budgetReference : String

open FinalNearIndexedFiniteInput public

compileFinalNearIndexedFiniteProducer :
  forall {S transport} ->
  (offInput : Direct.DirectLiteralOffTargetInput S transport) ->
  FinalNearIndexedFiniteInput offInput ->
  Eval.FiniteNearProducer
compileFinalNearIndexedFiniteProducer {S = S} {transport = transport}
    offInput input =
  Eval.finite-near-producer
    (route input)
    (routeAdmissible input)
    (preservation input)
    evaluation
    budget
  where
  finalNear : NearFar.Scalar S
  finalNear = Transport.nearResponseAt transport (Direct.chosenCutoff offInput)

  evaluation : Eval.SignedFiniteNearEvaluationSurface
  evaluation =
    Eval.signed-finite-near-evaluation-surface
      (NearFar.Scalar S)
      (Error input)
      finalNear
      (approximant input)
      (error input)
      (Within input)
      (withinEvaluation input)
      (evaluationReference input)

  budget : Eval.EvaluationProducesBudget evaluation
  budget =
    Eval.evaluation-produces-budget
      (Budget input)
      (nearBudget input)
      (ProducesRequiredUpper input)
      (producesRequiredUpper input)
      (budgetReference input)

compiledSignedNearValueIsFinalNear :
  forall {S transport} ->
  (offInput : Direct.DirectLiteralOffTargetInput S transport) ->
  (input : FinalNearIndexedFiniteInput offInput) ->
  Eval.SignedFiniteNearEvaluationSurface.signedNearValue
    (Eval.FiniteNearProducer.evaluation
      (compileFinalNearIndexedFiniteProducer offInput input))
  ≡ Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
compiledSignedNearValueIsFinalNear offInput input = refl

record FinalNearIndexedFiniteBoundary : Set where
  constructor final-near-indexed-finite-boundary
  field
    separateSignedValueToFinalNearWeldRequired : Bool
    separateSignedValueToFinalNearWeldRequiredIsFalse :
      separateSignedValueToFinalNearWeldRequired ≡ false

    finalNearSameObjectnessIsDefinitional : Bool
    finalNearSameObjectnessIsDefinitionalIsTrue :
      finalNearSameObjectnessIsDefinitional ≡ true

    evaluationReceiptStillRequired : Bool
    evaluationReceiptStillRequiredIsTrue :
      evaluationReceiptStillRequired ≡ true

    budgetExtractionStillRequiredByGenericFiniteProducer : Bool
    budgetExtractionStillRequiredByGenericFiniteProducerIsTrue :
      budgetExtractionStillRequiredByGenericFiniteProducer ≡ true

    literalFiniteSumRealisationStillRequired : Bool
    literalFiniteSumRealisationStillRequiredIsTrue :
      literalFiniteSumRealisationStillRequired ≡ true

    analyticPhaseInequalityPaidHere : Bool
    analyticPhaseInequalityPaidHereIsFalse : analyticPhaseInequalityPaidHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalFinalNearIndexedFiniteBoundary : FinalNearIndexedFiniteBoundary
canonicalFinalNearIndexedFiniteBoundary =
  final-near-indexed-finite-boundary
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "For the preferred direct route, index the carrier-neutral finite evaluation on final nearResponseAt(chosen J) itself. Then signedNearValue=finalNear is definitional rather than a fresh same-object theorem. A real Within evaluation receipt and budget extraction remain required, and the phase-visible representation theorem nearResponseAt(J)=finiteNearSum(cellResponse) remains genuinely unpaid. This module proves neither that representation theorem nor the post-crossing ClusterResponse inequality nor RH."
