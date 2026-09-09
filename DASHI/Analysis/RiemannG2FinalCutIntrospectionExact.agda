module DASHI.Analysis.RiemannG2FinalCutIntrospectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannG2FinalPoleQuotientMinimalAnalyticCutExact as Cut
import DASHI.Analysis.RiemannG2FinalPoleNearObserverRefinementExact as NearObserver
import DASHI.Analysis.RiemannG2ProofRelevantTargetTranslationModulationExact as PhaseLaw
import DASHI.Analysis.RiemannG2LiteralPhaseJointMarginCompilerExact as LiteralMargin

------------------------------------------------------------------------
-- INTROSPECTIVE BINDING FOR THE CURRENT RH HIGH-ZERO SCALAR LEAF
--
-- The final cut has already pruned the separate near/Gamma allowance leaves.
-- The surviving analytic theorem is exactly the independent literal complement
-- margin.  This owner prevents adjacent representation/downstream coordinates
-- or a visually compelling decomposition from being counted as payment.
------------------------------------------------------------------------

data RHFinalProducer : Set where
  independentLiteralComplementMarginProducer : RHFinalProducer
  crossProverTransportProducer : RHFinalProducer
  downstreamBalanceProducer : RHFinalProducer

producerForCoordinate : Cut.FinalCutCoordinate → RHFinalProducer
producerForCoordinate Cut.proveIndependentLiteralComplementMargin =
  independentLiteralComplementMarginProducer
producerForCoordinate Cut.transportCheckedLeanSplitFarToAgda =
  crossProverTransportProducer
producerForCoordinate Cut.sourceOrderReflexivity =
  crossProverTransportProducer
producerForCoordinate Cut.transportFinalSourceOrders =
  downstreamBalanceProducer
producerForCoordinate Cut.attachFinalClusterSameObject =
  downstreamBalanceProducer
producerForCoordinate Cut.assignConsumerChannelAllowances =
  downstreamBalanceProducer
producerForCoordinate Cut.proveChosenFiniteNearUpper =
  downstreamBalanceProducer
producerForCoordinate Cut.proveFreshGammaEnvelope =
  downstreamBalanceProducer
producerForCoordinate Cut.proveChosenNearLeavesFarAllowance =
  downstreamBalanceProducer
producerForCoordinate Cut.proveGammaFitsAssignedAllowance =
  downstreamBalanceProducer
producerForCoordinate Cut.rebuildNearFarBudgetFamilyForEveryCutoff =
  downstreamBalanceProducer
producerForCoordinate Cut.recoverDeterminantDirectPayment =
  downstreamBalanceProducer
producerForCoordinate Cut.rebuildFinalContradiction =
  downstreamBalanceProducer

record BoundRHFinalDemand : Set where
  constructor bound-rh-final-demand
  field
    liveCoordinate : Cut.FinalCutCoordinate
    liveCoordinateIsTerminalAnalyticLeaf :
      liveCoordinate ≡ Cut.proveIndependentLiteralComplementMargin
    coordinateClassIsAnalytic : Cut.coordinateClass liveCoordinate ≡ Cut.analytic
    producer : RHFinalProducer
    producerMatchesCoordinate : producer ≡ producerForCoordinate liveCoordinate
    analyticPaymentEstablished : Bool
    analyticPaymentEstablishedIsFalse : analyticPaymentEstablished ≡ false

open BoundRHFinalDemand public

currentBoundRHFinalDemand : BoundRHFinalDemand
currentBoundRHFinalDemand =
  bound-rh-final-demand
    Cut.proveIndependentLiteralComplementMargin
    refl
    refl
    independentLiteralComplementMarginProducer
    refl
    false
    refl

currentRHProducerTargetsExactAnalyticLeaf :
  producer currentBoundRHFinalDemand ≡ independentLiteralComplementMarginProducer
currentRHProducerTargetsExactAnalyticLeaf = refl

------------------------------------------------------------------------
-- SECOND-LEVEL INTROSPECTION: OBSERVER INSIDE THE LIVE SCALAR LEAF
--
-- The terminal leaf mentions D_near(J), but the final transport exposes that
-- object first as the scalar `nearResponseAt J`.  Count/envelope observations
-- collapse phase-distinct states, so the first universal refinement remains a
-- SAME-OBJECT literal model whose finite target-centred cosine sum is exactly
-- that final scalar.
--
-- Once that model is supplied, proof search branches.  A direct signed-cosine
-- theorem can act immediately on the literal sum.  A Fourier/modulation proof
-- additionally needs the proof-relevant b -> b-t translation/modulation law.
-- A full Weil target window is a still-stronger optional route.  None of these
-- representation refinements is the analytic payment itself.
------------------------------------------------------------------------

data RHInnerCoordinate : Set where
  abstractFinalNearScalar : RHInnerCoordinate
  countAndAbsoluteEnvelope : RHInnerCoordinate
  finalNearLiteralSameObjectModel : RHInnerCoordinate
  directPostCrossingSignedCosineEstimate : RHInnerCoordinate
  proofRelevantTargetTranslationModulation : RHInnerCoordinate
  taperRegularityForFourierOrIBP : RHInnerCoordinate
  fullWeilTargetWindowRealisation : RHInnerCoordinate
  literalJointComplementPayment : RHInnerCoordinate


data RHInnerState : Set where
  inadequateObservation : RHInnerState
  firstMissingCoordinate : RHInnerState
  routeSpecificRefinement : RHInnerState
  optionalStrongerRefinement : RHInnerState
  theoremPayment : RHInnerState

innerState : RHInnerCoordinate -> RHInnerState
innerState abstractFinalNearScalar = inadequateObservation
innerState countAndAbsoluteEnvelope = inadequateObservation
innerState finalNearLiteralSameObjectModel = firstMissingCoordinate
innerState directPostCrossingSignedCosineEstimate = theoremPayment
innerState proofRelevantTargetTranslationModulation = routeSpecificRefinement
innerState taperRegularityForFourierOrIBP = routeSpecificRefinement
innerState fullWeilTargetWindowRealisation = optionalStrongerRefinement
innerState literalJointComplementPayment = theoremPayment

currentInnerMissingCoordinate : RHInnerCoordinate
currentInnerMissingCoordinate = finalNearLiteralSameObjectModel

currentInnerMissingCoordinateIsFirst :
  innerState currentInnerMissingCoordinate ≡ firstMissingCoordinate
currentInnerMissingCoordinateIsFirst = refl

nearObserverAgreesPhaseIsFirstMissingCoordinate :
  NearObserver.FinalPoleNearObserverRefinementBoundary.targetRelativePhaseIsFirstMissingCoordinate
    NearObserver.canonicalFinalPoleNearObserverRefinementBoundary ≡ true
nearObserverAgreesPhaseIsFirstMissingCoordinate = refl

nearObserverAgreesFullWeilWindowIsStrongerThanPrimitiveNeed :
  NearObserver.FinalPoleNearObserverRefinementBoundary.fullWeilTargetWindowIsPrimitiveRequirementOfOneLeafConsumer
    NearObserver.canonicalFinalPoleNearObserverRefinementBoundary ≡ false
nearObserverAgreesFullWeilWindowIsStrongerThanPrimitiveNeed = refl

nearObserverAgreesLiteralModelIsNotPayment :
  NearObserver.FinalPoleNearObserverRefinementBoundary.literalModelAutomaticallyPaysJointMargin
    NearObserver.canonicalFinalPoleNearObserverRefinementBoundary ≡ false
nearObserverAgreesLiteralModelIsNotPayment = refl

proofRelevantPhaseLawIsNotInhabitedHere :
  PhaseLaw.ProofRelevantTranslationModulationBoundary.actualPoleQuotientIntertwinerInhabitedHere
    PhaseLaw.canonicalProofRelevantTranslationModulationBoundary ≡ false
proofRelevantPhaseLawIsNotInhabitedHere = refl

literalPhasePaymentIsTheoremBearingEndpoint :
  LiteralMargin.LiteralPhaseJointMarginBoundary.literalPhasePaymentCompilesCanonicalOneLeafMargin
    LiteralMargin.canonicalLiteralPhaseJointMarginBoundary ≡ true
literalPhasePaymentIsTheoremBearingEndpoint = refl

record BoundRHInnerRefinement : Set where
  constructor bound-rh-inner-refinement
  field
    parentDemand : BoundRHFinalDemand
    parentIsCurrentDemand : parentDemand ≡ currentBoundRHFinalDemand
    missingCoordinate : RHInnerCoordinate
    missingCoordinateIsCurrent : missingCoordinate ≡ currentInnerMissingCoordinate
    refinementRequired : Bool
    refinementRequiredIsTrue : refinementRequired ≡ true
    refinementPaysAnalyticMargin : Bool
    refinementPaysAnalyticMarginIsFalse : refinementPaysAnalyticMargin ≡ false

currentBoundRHInnerRefinement : BoundRHInnerRefinement
currentBoundRHInnerRefinement =
  bound-rh-inner-refinement
    currentBoundRHFinalDemand
    refl
    finalNearLiteralSameObjectModel
    refl
    true refl
    false refl

------------------------------------------------------------------------
-- Route admission.  Do not overconstrain the direct cosine route with Fourier
-- structure it does not consume.
------------------------------------------------------------------------

data PhaseProofRoute : Set where
  directCosineRoute : PhaseProofRoute
  translationModulationRoute : PhaseProofRoute
  integrationByPartsRoute : PhaseProofRoute
  fullWeilWindowRoute : PhaseProofRoute

routeNeedsTranslationModulation : PhaseProofRoute -> Bool
routeNeedsTranslationModulation directCosineRoute = false
routeNeedsTranslationModulation translationModulationRoute = true
routeNeedsTranslationModulation integrationByPartsRoute = true
routeNeedsTranslationModulation fullWeilWindowRoute = true

routeNeedsTaperRegularity : PhaseProofRoute -> Bool
routeNeedsTaperRegularity directCosineRoute = false
routeNeedsTaperRegularity translationModulationRoute = false
routeNeedsTaperRegularity integrationByPartsRoute = true
routeNeedsTaperRegularity fullWeilWindowRoute = false

directRouteDoesNotNeedTranslationModulation :
  routeNeedsTranslationModulation directCosineRoute ≡ false
directRouteDoesNotNeedTranslationModulation = refl

ibpRouteNeedsTaperRegularity :
  routeNeedsTaperRegularity integrationByPartsRoute ≡ true
ibpRouteNeedsTaperRegularity = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RepresentationTransportPaysAnalyticMargin : Set where
data FinalBalancePaysAnalyticMargin : Set where
data VisualizationPaysAnalyticMargin : Set where
data BoundProducerPaysAnalyticMargin : Set where
data LiteralNearRefinementPaysAnalyticMargin : Set where
data FourierLabelPaysSignedEstimate : Set where

representationTransportDoesNotPayAnalyticMargin :
  RepresentationTransportPaysAnalyticMargin → ⊥
representationTransportDoesNotPayAnalyticMargin ()

finalBalanceDoesNotPayAnalyticMargin : FinalBalancePaysAnalyticMargin → ⊥
finalBalanceDoesNotPayAnalyticMargin ()

visualizationDoesNotPayAnalyticMargin : VisualizationPaysAnalyticMargin → ⊥
visualizationDoesNotPayAnalyticMargin ()

boundProducerDoesNotPayAnalyticMargin : BoundProducerPaysAnalyticMargin → ⊥
boundProducerDoesNotPayAnalyticMargin ()

literalNearRefinementDoesNotPayAnalyticMargin :
  LiteralNearRefinementPaysAnalyticMargin → ⊥
literalNearRefinementDoesNotPayAnalyticMargin ()

fourierLabelDoesNotPaySignedEstimate : FourierLabelPaysSignedEstimate → ⊥
fourierLabelDoesNotPaySignedEstimate ()
