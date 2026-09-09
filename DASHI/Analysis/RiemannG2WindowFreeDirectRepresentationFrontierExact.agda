module DASHI.Analysis.RiemannG2WindowFreeDirectRepresentationFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotlePoleQuotientFiniteNearEvaluationBidiExact as Eval
import DASHI.Analysis.RiemannG2WindowFreeFiniteNearFinalModelCompilerExact as WindowFree
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as Final

------------------------------------------------------------------------
-- DIRECT REPRESENTATION FRONTIER BELOW THE HIGH ANALYTIC THEOREM
--
-- Keep representation acquisition separate from the theorem
--
--   literalNear + far + Gamma < ClusterResponse.
--
-- The carrier-neutral FiniteNearProducer owns an actual signed evaluation, but
-- it does not by itself expose the literal kernel nor identify that signed value
-- with final nearResponseAt(J).  The window-free compiler makes those exact
-- same-object debts explicit without importing the stronger target-window route.
------------------------------------------------------------------------

data DirectRepresentationCoordinate : Set where
  recoverCarrierNeutralFiniteNearProducer : DirectRepresentationCoordinate
  realiseLiteralPoleQuotientKernel : DirectRepresentationCoordinate
  weldSignedEvaluationToLiteralFiniteSum : DirectRepresentationCoordinate
  weldSignedEvaluationToFinalNearResponse : DirectRepresentationCoordinate
  compileFinalPoleNearLiteralModel : DirectRepresentationCoordinate
  recoverActualSelectedPoleNearProducer : DirectRepresentationCoordinate
  recoverDeterminantDirectProducer : DirectRepresentationCoordinate

data DirectRepresentationState : Set where
  live : DirectRepresentationState
  compilerOutput : DirectRepresentationState
  optionalStrongerRoute : DirectRepresentationState
  compatibilityOnly : DirectRepresentationState

coordinateState : DirectRepresentationCoordinate -> DirectRepresentationState
coordinateState recoverCarrierNeutralFiniteNearProducer = live
coordinateState realiseLiteralPoleQuotientKernel = live
coordinateState weldSignedEvaluationToLiteralFiniteSum = live
coordinateState weldSignedEvaluationToFinalNearResponse = live
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

windowFreeCompilerRejectsExplicitWindowPrerequisite :
  WindowFree.WindowFreeFiniteNearFinalBoundary.explicitTargetWindowRequiredForDirectSameObjectWeld
    WindowFree.canonicalWindowFreeFiniteNearFinalBoundary ≡ false
windowFreeCompilerRejectsExplicitWindowPrerequisite = refl

windowFreeCompilerRejectsDeterminantPrerequisite :
  WindowFree.WindowFreeFiniteNearFinalBoundary.determinantDirectConsumerRequired
    WindowFree.canonicalWindowFreeFiniteNearFinalBoundary ≡ false
windowFreeCompilerRejectsDeterminantPrerequisite = refl

kernelAndScalarWeldAreDistinct :
  WindowFree.WindowFreeFiniteNearFinalBoundary.literalKernelAndFinalScalarWeldAreDistinctDebts
    WindowFree.canonicalWindowFreeFiniteNearFinalBoundary ≡ true
kernelAndScalarWeldAreDistinct = refl

finiteProducerDoesNotConstructKernelAlone :
  WindowFree.WindowFreeFiniteNearFinalBoundary.carrierNeutralFiniteProducerAloneBuildsLiteralKernel
    WindowFree.canonicalWindowFreeFiniteNearFinalBoundary ≡ false
finiteProducerDoesNotConstructKernelAlone = refl

finiteProducerDoesNotIdentifyFinalNearAlone :
  WindowFree.WindowFreeFiniteNearFinalBoundary.carrierNeutralFiniteProducerAloneIdentifiesFinalNearScalar
    WindowFree.canonicalWindowFreeFiniteNearFinalBoundary ≡ false
finiteProducerDoesNotIdentifyFinalNearAlone = refl

kernelAndWeldCompileExistingFinalModel :
  WindowFree.WindowFreeFiniteNearFinalBoundary.kernelPlusTwoSameObjectEqualitiesCompileFinalLiteralModel
    WindowFree.canonicalWindowFreeFiniteNearFinalBoundary ≡ true
kernelAndWeldCompileExistingFinalModel = refl

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

    carrierNeutralSignedEvaluationIsSufficientWithoutSameObjectWeld : Bool
    carrierNeutralSignedEvaluationIsSufficientWithoutSameObjectWeldIsFalse :
      carrierNeutralSignedEvaluationIsSufficientWithoutSameObjectWeld ≡ false

    literalKernelRealisationStillRequired : Bool
    literalKernelRealisationStillRequiredIsTrue :
      literalKernelRealisationStillRequired ≡ true

    signedValueToLiteralSumEqualityStillRequired : Bool
    signedValueToLiteralSumEqualityStillRequiredIsTrue :
      signedValueToLiteralSumEqualityStillRequired ≡ true

    signedValueToFinalNearEqualityStillRequired : Bool
    signedValueToFinalNearEqualityStillRequiredIsTrue :
      signedValueToFinalNearEqualityStillRequired ≡ true

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
    true refl
    false refl
    false refl
    "Stay window-free on the preferred direct route: recover one carrier-neutral FiniteNearProducer, realize the literal universal-pole-quotient kernel, prove signedNearValue=literalFiniteNearValue and signedNearValue=final nearResponseAt(chosen J), then compile the existing FinalPoleNearLiteralModel. ActualSelectedPoleNearProducer is an optional stronger explicit-formula route and the determinant-q DirectFinitePoleNearProducer is compatibility-only. None of these representation payments proves the post-crossing strict ClusterResponse inequality or RH."
