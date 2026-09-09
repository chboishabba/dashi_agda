module DASHI.Analysis.RiemannG2WindowFreeDirectRepresentationFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval
import DASHI.Analysis.RiemannG2FinalNearIndexedFiniteProducerExact as FinalFinite
import DASHI.Analysis.RiemannG2FinalNearIndexedLiteralModelCompilerExact as FinalIndexed
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Final

------------------------------------------------------------------------
-- DIRECT REPRESENTATION FRONTIER BELOW THE HIGH ANALYTIC THEOREM
--
-- Current shortest direct route:
--
--   final-near-indexed carrier-neutral evaluation
--   + literal universal-pole-quotient kernel
--   + nearResponseAt(J) = finiteNearSum(cellResponse)
--   -> existing FinalPoleNearLiteralModel.
--
-- The evaluator is indexed on final nearResponseAt(J), so the older standalone
-- signed-value/final-near same-object weld is definitionally eliminated.
------------------------------------------------------------------------

data DirectRepresentationCoordinate : Set where
  recoverFinalNearIndexedFiniteEvaluation : DirectRepresentationCoordinate
  realiseLiteralPoleQuotientKernel : DirectRepresentationCoordinate
  proveFinalNearEqualsLiteralFiniteSum : DirectRepresentationCoordinate
  compileFinalPoleNearLiteralModel : DirectRepresentationCoordinate
  recoverActualSelectedPoleNearProducer : DirectRepresentationCoordinate
  recoverDeterminantDirectProducer : DirectRepresentationCoordinate

data DirectRepresentationState : Set where
  live : DirectRepresentationState
  compilerOutput : DirectRepresentationState
  optionalStrongerRoute : DirectRepresentationState
  compatibilityOnly : DirectRepresentationState

coordinateState : DirectRepresentationCoordinate -> DirectRepresentationState
coordinateState recoverFinalNearIndexedFiniteEvaluation = live
coordinateState realiseLiteralPoleQuotientKernel = live
coordinateState proveFinalNearEqualsLiteralFiniteSum = live
coordinateState compileFinalPoleNearLiteralModel = compilerOutput
coordinateState recoverActualSelectedPoleNearProducer = optionalStrongerRoute
coordinateState recoverDeterminantDirectProducer = compatibilityOnly

finalModelCompilationIsDownstream :
  coordinateState compileFinalPoleNearLiteralModel ≡ compilerOutput
finalModelCompilationIsDownstream = refl

explicitWindowIsOptionalStrongerRoute :
  coordinateState recoverActualSelectedPoleNearProducer ≡ optionalStrongerRoute
explicitWindowIsOptionalStrongerRoute = refl

determinantProducerIsCompatibilityOnly :
  coordinateState recoverDeterminantDirectProducer ≡ compatibilityOnly
determinantProducerIsCompatibilityOnly = refl

finalNearSameObjectWeldEliminated :
  FinalFinite.FinalNearIndexedFiniteBoundary.separateSignedValueToFinalNearWeldRequired
    FinalFinite.canonicalFinalNearIndexedFiniteBoundary ≡ false
finalNearSameObjectWeldEliminated = refl

oneScalarRepresentationTheoremRemains :
  FinalIndexed.FinalNearIndexedLiteralModelBoundary.finalNearToLiteralFiniteSumIsSingleScalarRepresentationTheorem
    FinalIndexed.canonicalFinalNearIndexedLiteralModelBoundary ≡ true
oneScalarRepresentationTheoremRemains = refl

explicitWindowNotRequired :
  FinalIndexed.FinalNearIndexedLiteralModelBoundary.explicitWindowRequired
    FinalIndexed.canonicalFinalNearIndexedLiteralModelBoundary ≡ false
explicitWindowNotRequired = refl

determinantConsumerNotRequired :
  FinalIndexed.FinalNearIndexedLiteralModelBoundary.determinantConsumerRequired
    FinalIndexed.canonicalFinalNearIndexedLiteralModelBoundary ≡ false
determinantConsumerNotRequired = refl

finalLiteralModelIsCompilerOutput :
  FinalIndexed.FinalNearIndexedLiteralModelBoundary.existingFinalLiteralModelIsCompilerOutput
    FinalIndexed.canonicalFinalNearIndexedLiteralModelBoundary ≡ true
finalLiteralModelIsCompilerOutput = refl

finiteEvaluationStillOpen :
  Eval.FiniteNearEvaluationBoundary.finiteNearEvaluationClosed
    Eval.canonicalFiniteNearEvaluationBoundary ≡ false
finiteEvaluationStillOpen = refl

finalLiteralModelStillUninhabited :
  Final.FinalPoleNearObserverRefinementBoundary.literalFinalModelInhabitedHere
    Final.canonicalFinalPoleNearObserverRefinementBoundary ≡ false
finalLiteralModelStillUninhabited = refl

record WindowFreeDirectRepresentationBoundary : Set where
  constructor window-free-direct-representation-boundary
  field
    directRouteNeedsExplicitWeilWindow : Bool
    directRouteNeedsExplicitWeilWindowIsFalse :
      directRouteNeedsExplicitWeilWindow ≡ false

    directRouteNeedsDeterminantConsumerPayment : Bool
    directRouteNeedsDeterminantConsumerPaymentIsFalse :
      directRouteNeedsDeterminantConsumerPayment ≡ false

    separateSignedValueToFinalNearWeldStillRequired : Bool
    separateSignedValueToFinalNearWeldStillRequiredIsFalse :
      separateSignedValueToFinalNearWeldStillRequired ≡ false

    literalKernelRealisationStillRequired : Bool
    literalKernelRealisationStillRequiredIsTrue :
      literalKernelRealisationStillRequired ≡ true

    finalNearEqualsLiteralFiniteSumStillRequired : Bool
    finalNearEqualsLiteralFiniteSumStillRequiredIsTrue :
      finalNearEqualsLiteralFiniteSumStillRequired ≡ true

    finalLiteralModelIsCompilerOutputAfterThese : Bool
    finalLiteralModelIsCompilerOutputAfterTheseIsTrue :
      finalLiteralModelIsCompilerOutputAfterThese ≡ true

    analyticPhaseInequalityPaidHere : Bool
    analyticPhaseInequalityPaidHereIsFalse : analyticPhaseInequalityPaidHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    shortestDirectRepresentationPath : String

canonicalWindowFreeDirectRepresentationBoundary :
  WindowFreeDirectRepresentationBoundary
canonicalWindowFreeDirectRepresentationBoundary =
  window-free-direct-representation-boundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "Stay window-free and index the carrier-neutral evaluator directly on final nearResponseAt(chosen J). Realize the literal universal-pole-quotient kernel and prove the single scalar representation theorem nearResponseAt(J)=finiteNearSum(cellResponse). The older signed-value/final-near weld, explicit selected Weil window and determinant-q consumer are not required. These representation payments compile the existing FinalPoleNearLiteralModel but do not prove the post-crossing strict ClusterResponse inequality or RH."
